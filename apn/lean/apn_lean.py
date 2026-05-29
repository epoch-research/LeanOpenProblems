#!/usr/bin/env python3
"""Sandbox-side Lean verification daemon and client.

This script runs *inside* the Lean Docker sandbox. It wraps a warm PyPantograph
``Server`` (which holds a single ``pantograph-repl`` subprocess with Mathlib
loaded) so that the many compile calls a proving episode makes do not each pay
the cost of importing Mathlib.

Two subcommands:

* ``serve``  -- start the warm server and listen on a Unix socket. Run once per
  sample (e.g. from the sample's setup script).
* ``client`` -- read one JSON request from stdin, forward it to the daemon
  (starting the daemon if it is not already running), and print the JSON
  response to stdout. This is what the Inspect-side verifier invokes.

Protocol (newline-delimited JSON; ``json.dumps`` keeps each message on one
line):

    request : {"op": "compile", "code": "<lean>"}
            | {"op": "axioms",  "code": "<lean>", "decls": ["foo", ...]}

    compile response : {"ok": bool, "has_sorry": bool, "system_error": str|null,
                        "diagnostics": [{"severity","message","line","column"}]}
    axioms response  : {"axioms": {"foo": ["propext", ...]}, "error": str|null}

The daemon is intentionally single-connection-at-a-time: the underlying repl is
a single Lean process and must be driven serially, so concurrent prover
subagents queue here. That matches the throughput ceiling of the compiler.
"""

from __future__ import annotations

import asyncio
import fcntl
import json
import os
import re
import socket
import subprocess
import sys
import time
from typing import Any

SOCKET_PATH = os.environ.get("APN_LEAN_SOCKET", "/tmp/apn_lean.sock")
LOCK_PATH = SOCKET_PATH + ".lock"
LOG_PATH = os.environ.get("APN_LEAN_LOG", "/tmp/apn_lean.log")
PROJECT_PATH = os.environ.get("APN_LEAN_PROJECT", "/workspace/leanproject")
IMPORTS = ["Mathlib"]
# Mathlib import + a hard proof can take a while; give the repl room.
SERVER_TIMEOUT = int(os.environ.get("APN_LEAN_TIMEOUT", "600"))
# A single JSON message can hold a large Lean file, so the stream reader needs a
# generous line limit (default asyncio limit is only 64 KiB).
STREAM_LIMIT = 64 * 1024 * 1024

_AXIOM_DEPENDS_RE = re.compile(
    r"^'?(?P<name>[^']+?)'? depends on axioms: \[(?P<axioms>.*)\]\s*$"
)
_AXIOM_NONE_RE = re.compile(r"^'?(?P<name>[^']+?)'? does not depend on any axioms")

_SEVERITY_MAP = {"information": "info", "warning": "warning", "error": "error"}


# --------------------------------------------------------------------------- #
# Pure parsing helpers (unit-tested in tests/test_apn_lean.py)                 #
# --------------------------------------------------------------------------- #


def normalize_severity(severity: str) -> str:
    return _SEVERITY_MAP.get(severity, "info")


def message_indicates_sorry(text: str) -> bool:
    # Lean's warning is "declaration uses `sorry`" (backticks in recent
    # toolchains, single quotes in older ones).
    return bool(re.search(r"uses\s+[`']?sorry[`']?", text))


def summarize_compile(
    messages: list[tuple[str, str, int | None, int | None]],
) -> dict[str, Any]:
    """Turn ``(severity, data, line, column)`` tuples into a compile response."""
    diagnostics: list[dict[str, Any]] = []
    has_sorry = False
    for severity, data, line, column in messages:
        norm = normalize_severity(severity)
        diagnostics.append(
            {"severity": norm, "message": data, "line": line, "column": column}
        )
        if message_indicates_sorry(data):
            has_sorry = True
    ok = not any(d["severity"] == "error" for d in diagnostics)
    return {
        "ok": ok,
        "has_sorry": has_sorry,
        "diagnostics": diagnostics,
        "system_error": None,
    }


def parse_axiom_messages(
    messages: list[tuple[str, str]], decls: list[str]
) -> dict[str, Any]:
    """Parse ``#print axioms`` output from ``(severity, data)`` message tuples."""
    found: dict[str, list[str]] = {}
    errors: list[str] = []
    for severity, data in messages:
        text = data.strip()
        if normalize_severity(severity) == "error":
            errors.append(text)
            continue
        depends = _AXIOM_DEPENDS_RE.match(text)
        if depends:
            names = [a.strip() for a in depends.group("axioms").split(",") if a.strip()]
            found[depends.group("name")] = names
            continue
        none_match = _AXIOM_NONE_RE.match(text)
        if none_match:
            found[none_match.group("name")] = []
    missing = [d for d in decls if d not in found]
    error: str | None = "; ".join(errors) if (missing and errors) else None
    return {"axioms": found, "error": error}


# --------------------------------------------------------------------------- #
# Daemon                                                                       #
# --------------------------------------------------------------------------- #


def _log(message: str) -> None:
    try:
        with open(LOG_PATH, "a") as handle:
            handle.write(f"[{time.time():.0f}] {message}\n")
    except OSError:
        pass


def _collect_messages(units: Any) -> list[tuple[str, str, int | None, int | None]]:
    messages: list[tuple[str, str, int | None, int | None]] = []
    for unit in units:
        for message in unit.messages:
            line = message.pos.line if message.pos else None
            column = message.pos.column if message.pos else None
            messages.append((str(message.severity), message.data, line, column))
    return messages


async def _compile(server: Any, code: str) -> dict[str, Any]:
    units = await server.check_compile_async(code)
    return summarize_compile(_collect_messages(units))


async def _axioms(server: Any, code: str, decls: list[str]) -> dict[str, Any]:
    queries = "\n".join(f"#print axioms {decl}" for decl in decls)
    full = code + "\n" + queries + "\n"
    units = await server.check_compile_async(full)
    messages = [(sev, data) for sev, data, _line, _col in _collect_messages(units)]
    return parse_axiom_messages(messages, decls)


async def _process(server: Any, request: dict[str, Any]) -> dict[str, Any]:
    op = request.get("op")
    try:
        if op == "compile":
            return await _compile(server, request["code"])
        if op == "axioms":
            return await _axioms(server, request["code"], request.get("decls", []))
        return {"system_error": f"unknown op: {op!r}"}
    except Exception as exc:  # noqa: BLE001 - surfaced to the caller as feedback
        _log(f"error processing {op}: {exc!r}")
        # The repl may be in a bad state; restart it for the next request.
        try:
            await server.restart_async()
        except Exception as restart_exc:  # noqa: BLE001
            _log(f"restart failed: {restart_exc!r}")
        return {"system_error": f"{type(exc).__name__}: {exc}"}


async def _serve() -> None:
    from pantograph import Server  # imported lazily; only present in the sandbox

    _log(f"starting server (project={PROJECT_PATH})")
    server = await Server.create(
        imports=IMPORTS, project_path=PROJECT_PATH, timeout=SERVER_TIMEOUT
    )
    # Warm the environment so the first real request is fast.
    try:
        await server.check_compile_async("example : True := trivial")
        _log("warmup compile ok")
    except Exception as exc:  # noqa: BLE001
        _log(f"warmup failed: {exc!r}")

    lock = asyncio.Lock()

    async def handle(
        reader: asyncio.StreamReader, writer: asyncio.StreamWriter
    ) -> None:
        try:
            line = await reader.readline()
            if not line:
                return
            request = json.loads(line.decode())
            async with lock:
                response = await _process(server, request)
        except Exception as exc:  # noqa: BLE001
            response = {"system_error": f"daemon: {type(exc).__name__}: {exc}"}
        writer.write((json.dumps(response, ensure_ascii=False) + "\n").encode())
        await writer.drain()
        writer.close()

    if os.path.exists(SOCKET_PATH):
        os.unlink(SOCKET_PATH)
    srv = await asyncio.start_unix_server(handle, path=SOCKET_PATH, limit=STREAM_LIMIT)
    _log("listening")
    async with srv:
        await srv.serve_forever()


# --------------------------------------------------------------------------- #
# Client                                                                       #
# --------------------------------------------------------------------------- #


def _socket_alive() -> bool:
    if not os.path.exists(SOCKET_PATH):
        return False
    probe = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    try:
        probe.connect(SOCKET_PATH)
        return True
    except OSError:
        return False
    finally:
        probe.close()


def _ensure_daemon(startup_timeout: float = 900.0) -> None:
    if _socket_alive():
        return
    # Serialize startup so concurrent clients do not race to spawn daemons.
    with open(LOCK_PATH, "w") as lock_file:
        fcntl.flock(lock_file, fcntl.LOCK_EX)
        if _socket_alive():
            return
        log = open(LOG_PATH, "a")
        subprocess.Popen(
            [sys.executable, os.path.abspath(__file__), "serve"],
            stdout=log,
            stderr=log,
            start_new_session=True,
        )
        deadline = time.time() + startup_timeout
        while time.time() < deadline:
            if _socket_alive():
                return
            time.sleep(0.5)
        raise TimeoutError("Lean daemon did not start within the timeout")


def _recv_line(conn: socket.socket) -> bytes:
    chunks: list[bytes] = []
    while True:
        chunk = conn.recv(65536)
        if not chunk:
            break
        chunks.append(chunk)
        if chunk.endswith(b"\n"):
            break
    return b"".join(chunks)


def _client() -> int:
    request = sys.stdin.buffer.read().rstrip(b"\n") + b"\n"
    try:
        _ensure_daemon()
    except Exception as exc:  # noqa: BLE001
        print(json.dumps({"system_error": f"daemon start failed: {exc}"}))
        return 0
    conn = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    conn.connect(SOCKET_PATH)
    try:
        conn.sendall(request)
        response = _recv_line(conn)
    finally:
        conn.close()
    sys.stdout.buffer.write(response)
    return 0


def main(argv: list[str]) -> int:
    if len(argv) < 2 or argv[1] not in {"serve", "client"}:
        print("usage: apn_lean.py [serve|client]", file=sys.stderr)
        return 2
    if argv[1] == "serve":
        asyncio.run(_serve())
        return 0
    return _client()


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
