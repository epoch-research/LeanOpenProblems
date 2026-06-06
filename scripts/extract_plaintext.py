"""Extract the agent transcript from an apn ``.eval`` log into plain text.

This is the apn counterpart of a generic Inspect log dumper, adapted to how
this repo runs. Two things differ from a vanilla extractor:

* **The proof is one file, not a workspace tree.** The agent edits a single Lean
  file in the sandbox (``apn.agent.PROOF_PATH``); the scorer reads it back and
  stores the final text in ``score.answer``. So instead of reconstructing a
  directory we just write that submission out as ``submission.lean``.

* **The transcript lives in events, not ``sample.messages``.** ``apn.agent``
  runs the proving agent via ``inspect_ai.agent.run`` in its own ``AgentState``,
  so the top-level ``TaskState.messages`` only ever holds the initial prompt.
  The real conversation is reconstructed from the sample's ``model`` events
  (each carries its turn's input messages plus the assistant output), deduped by
  message id in event order.

  ``deepagent`` also spawns subagents (e.g. ``research``) whose turns interleave
  in the event stream. We keep only the **main loop**: a model event belongs to
  the main loop iff its enclosing span chain contains exactly one ``agent`` span
  (the outermost). Subagent turns nest a second ``agent`` span and are dropped.
  For the plain ``react`` loop there are no subagents, so everything is kept.

Usage::

    python scripts/extract_plaintext.py logs/run.eval
    python scripts/extract_plaintext.py logs/some-dir/ -o /tmp/out
    python scripts/extract_plaintext.py logs/run.eval --list-samples
    python scripts/extract_plaintext.py logs/run.eval -s a325046_...
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path

from inspect_ai.log import (
    EvalSample,
    read_eval_log,
    read_eval_log_sample,
    read_eval_log_sample_summaries,
    resolve_sample_attachments,
)
from inspect_ai.model import (
    ChatMessage,
    ChatMessageAssistant,
    ChatMessageSystem,
    ChatMessageTool,
    ChatMessageUser,
    ContentImage,
    ContentReasoning,
    ContentText,
)
from inspect_ai.tool import ToolCall


def extract_text(msg: ChatMessage) -> str:
    content = msg.content
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        parts = []
        for block in content:
            if isinstance(block, ContentText):
                parts.append(block.text)
            elif isinstance(block, ContentReasoning):
                if block.redacted:
                    parts.append(block.summary if block.summary is not None else "[redacted reasoning]")
                else:
                    parts.append(block.reasoning)
            elif isinstance(block, ContentImage):
                parts.append("[image]")
            elif isinstance(block, str):
                parts.append(block)
            else:
                parts.append(f"[{type(block).__name__}]")
        return "\n".join(parts)
    return str(content) if content else ""


def format_tool_call(tc: ToolCall) -> str:
    """Render a tool call the way the apn agent issues them.

    The proving agent's tools are Inspect's built-in ``text_editor`` and this
    repo's ``bash`` (whose argument is ``command``; see ``apn.tools``), plus the
    ``deepagent`` extras -- ``todo_write``, the ``agent`` subagent-spawn call,
    and the file helpers (``read_file``/``list_files``/``grep``). ``submit_proof``
    takes no arguments (the edited file is the submission; see ``apn.agent``).
    Anything unrecognised falls back to a compact JSON dump.
    """
    fn = tc.function
    args = tc.arguments

    if fn == "bash" and "command" in args:
        return f">>> bash\n```\n{args['command']}\n```"

    if fn == "text_editor":
        cmd = args.get("command", "")
        path = args.get("path", "")
        parts = [f">>> text_editor {cmd} {path}".strip()]
        old = args.get("old_str", "")
        new = args.get("new_str", "")
        file_text = args.get("file_text", "")
        if cmd == "view":
            view_range = args.get("view_range")
            if view_range:
                parts.append(f"lines {view_range}")
        elif cmd == "str_replace" and old:
            parts.append(f"OLD:\n{old}\nNEW:\n{new}")
        elif cmd == "insert":
            parts.append(f"INSERT after line {args.get('insert_line', '')}:\n{new}")
        elif cmd == "create" and file_text:
            parts.append(file_text)
        else:
            remaining = {k: v for k, v in args.items() if k not in ("command", "path")}
            if remaining:
                parts.append(json.dumps(remaining, ensure_ascii=False))
        return "\n".join(parts)

    if fn == "submit_proof":
        return ">>> submit_proof()"

    if fn == "agent":
        # deepagent spawning a subagent: surface who and the task, dump the rest.
        subagent = args.get("subagent_type", "")
        header = f">>> agent({subagent})".replace("()", "()") if subagent else ">>> agent"
        parts = [header]
        desc = args.get("task_description") or args.get("prompt")
        if desc:
            parts.append(str(desc))
        return "\n".join(parts)

    if fn == "todo_write":
        return f">>> todo_write\n{json.dumps(args.get('todos', args), ensure_ascii=False, indent=2)}"

    return f">>> {fn}({json.dumps(args, ensure_ascii=False)})"


def get_primary_model(messages: list[ChatMessage]) -> str | None:
    models = [msg.model for msg in messages if isinstance(msg, ChatMessageAssistant) and msg.model]
    if not models:
        return None
    return Counter(models).most_common(1)[0][0]


def format_message(msg: ChatMessage, idx: int, primary_model: str | None = None) -> str:
    n = idx + 1
    lines: list[str] = []

    if isinstance(msg, ChatMessageSystem):
        lines.append(f"[{n}] === SYSTEM ===")
        lines.append(extract_text(msg))

    elif isinstance(msg, ChatMessageUser):
        text = extract_text(msg)
        source = msg.source or ""
        tag = f" ({source})" if source and source != "input" else ""
        lines.append(f"[{n}] --- USER{tag} ---")
        lines.append(text)

    elif isinstance(msg, ChatMessageAssistant):
        model = msg.model or ""
        model_tag = f" [{model}]" if model and model != primary_model else ""
        lines.append(f"[{n}] --- ASSISTANT{model_tag} ---")
        text = extract_text(msg)
        if text:
            lines.append(text)
        if msg.tool_calls:
            for tc in msg.tool_calls:
                lines.append(format_tool_call(tc))

    elif isinstance(msg, ChatMessageTool):
        lines.append(f"[{n}] --- TOOL ({msg.function}) ---")
        if msg.error:
            err_msg = getattr(msg.error, "message", None) or str(msg.error)
            lines.append(f"[ERROR] {err_msg}")
        text = extract_text(msg)
        if text:
            lines.append(text)

    else:
        lines.append(f"[{n}] --- {msg.role.upper()} ---")
        text = extract_text(msg)
        if text:
            lines.append(text)

    return "\n".join(lines)


def _is_compaction_summary(msg: ChatMessage) -> bool:
    return bool(msg.metadata and msg.metadata.get("summary"))


def _extract_summary_body(text: str) -> str:
    m = re.search(r"<summary>\s*\n?(.*?)\n?\s*</summary>", text, re.DOTALL)
    return m.group(1).strip() if m else text


def _agent_depth(span_id: str | None, parent: dict[str, str | None], span_type: dict[str, str | None]) -> int:
    """Number of ``agent`` spans on the path from ``span_id`` up to the root."""
    depth = 0
    sid = span_id
    while sid is not None:
        if span_type.get(sid) == "agent":
            depth += 1
        sid = parent.get(sid)
    return depth


def main_loop_messages(sample: EvalSample) -> list[ChatMessage]:
    """Reconstruct the main agent loop's conversation from the sample's events.

    The conversation is not in ``sample.messages`` (apn runs the agent via
    ``run`` in its own state); we rebuild it from ``model`` events, deduping
    messages by id in event order. Only the outermost agent loop is kept --
    a model event whose span chain has more than the minimum number of ``agent``
    spans is a subagent turn and is skipped. See the module docstring.
    """
    spans = [e for e in sample.events if e.event == "span_begin"]
    parent = {s.id: s.parent_id for s in spans}
    span_type = {s.id: s.type for s in spans}

    model_events = [e for e in sample.events if e.event == "model"]
    if not model_events:
        return []
    depths = [_agent_depth(e.span_id, parent, span_type) for e in model_events]
    main_depth = min(depths)

    seen: set[str] = set()
    messages: list[ChatMessage] = []
    fallback = 0

    def add(m: ChatMessage) -> None:
        nonlocal fallback
        mid = getattr(m, "id", None)
        if mid is None:
            fallback += 1
            mid = f"__nofallbackid_{fallback}"
        if mid in seen:
            return
        seen.add(mid)
        messages.append(m)

    for event, depth in zip(model_events, depths):
        if depth != main_depth:
            continue
        for m in event.input or []:
            add(m)
        if event.output and event.output.choices:
            add(event.output.choices[0].message)

    return messages


def _get_enumerated_messages(messages: list[ChatMessage]) -> list[tuple[int, ChatMessage]]:
    """Group tool messages under the assistant message that triggered them.

    Mirrors the Inspect UI's message grouping: a tool result shares the index of
    the preceding non-tool message rather than getting its own.
    """
    results = []
    index = -1
    for message in messages:
        if index == -1 or not isinstance(message, ChatMessageTool):
            index += 1
        results.append((index, message))
    return results


def _emit(out):
    def emit(*lines: str):
        for line in lines:
            out.write(line)
            out.write("\n")

    return emit


def _write_transcript(messages: list[ChatMessage], out) -> None:
    emit = _emit(out)
    enumerated = _get_enumerated_messages(messages)
    primary_model = get_primary_model(messages)
    for i, msg in enumerated:
        emit(format_message(msg, i, primary_model), "")


def _write_compactions(messages: list[ChatMessage], out) -> None:
    emit = _emit(out)
    enumerated = _get_enumerated_messages(messages)
    summaries = [(i, msg) for i, msg in enumerated if _is_compaction_summary(msg)]
    if not summaries:
        emit("(no compaction summaries found)", "")
        return
    for seq, (idx, msg) in enumerate(summaries, 1):
        body = _extract_summary_body(extract_text(msg))
        emit(f"--- Compaction {seq}/{len(summaries)} (after message {idx + 1}) ---", body, "")


def _proof_submission(sample: EvalSample) -> str | None:
    """The agent's final proof text, taken from the proof scorer's answer."""
    scores = sample.scores or {}
    proof = scores.get("proof_scorer")
    if proof and proof.answer:
        return proof.answer
    for score in scores.values():
        if score.answer:
            return score.answer
    return None


def _write_scores(sample: EvalSample, out) -> None:
    emit = _emit(out)
    if not sample.scores:
        return
    emit("=== SCORES ===")
    for scorer_name, score in sample.scores.items():
        emit(f"{scorer_name}: {score.value}")
        stage = (score.metadata or {}).get("stage")
        if stage:
            emit(f"  stage: {stage}")
        if score.explanation:
            indented = "\n".join(f"  {line}" for line in score.explanation.splitlines())
            emit(indented)
    emit("")


def _write_scores_json(sample: EvalSample, out) -> None:
    payload = {
        name: {
            "value": score.value,
            "explanation": score.explanation,
            "metadata": score.metadata,
        }
        for name, score in (sample.scores or {}).items()
    }
    json.dump(payload, out, indent=2, ensure_ascii=False, default=str)
    out.write("\n")


def _write_eval_scores_json(eval_path: Path, out) -> None:
    log = read_eval_log(str(eval_path), header_only=True)
    scores = log.results.model_dump(include={"scores"}, mode="json")["scores"] if log.results else []
    json.dump(scores, out, indent=2, ensure_ascii=False, default=str)
    out.write("\n")


def _write_info(sample: EvalSample, out) -> None:
    metadata = sample.metadata or {}
    info = {
        "id": str(sample.id),
        "epoch": sample.epoch,
        "uuid": sample.uuid,
        "target": sample.target,
        "error": sample.model_dump(include={"error"}, mode="json")["error"],
        "limit": sample.model_dump(include={"limit"}, mode="json")["limit"],
        "model_usage": sample.model_dump(include={"model_usage"}, mode="json")["model_usage"],
        # apn/OEIS-specific provenance (see apn.dataset.oeis_dataset).
        "oeis_id": metadata.get("oeis_id"),
        "source_file": metadata.get("source_file"),
        "alt_files": metadata.get("alt_files"),
        "target_declarations": metadata.get("target_declarations"),
    }
    json.dump(info, out, indent=2, ensure_ascii=False, default=str)
    out.write("\n")


def list_samples(eval_path: str | Path) -> list[str]:
    summaries = read_eval_log_sample_summaries(str(eval_path))
    return sorted({str(s.id) for s in summaries})


def _iter_samples(eval_path: Path, sample_ids: set[str] | None):
    eval_path_str = str(eval_path)
    log = read_eval_log(eval_path_str, header_only=True)
    epochs = log.eval.config.epochs or 1
    for s in read_eval_log_sample_summaries(eval_path_str):
        sid = str(s.id)
        if sample_ids is not None and sid not in sample_ids:
            continue
        # Read the full sample: the transcript is reconstructed from events
        # (see main_loop_messages), so events must not be excluded.
        # resolve_sample_attachments inlines the ``attachment://<hash>`` blobs
        # (bash commands, tool outputs, long prompts) that Inspect stores out of
        # line -- without it the transcript is full of bare attachment refs.
        sample = resolve_sample_attachments(
            read_eval_log_sample(eval_path_str, id=s.id, epoch=s.epoch)
        )
        stem = f"{sid}_ep{sample.epoch:03d}" if epochs > 1 else sid
        yield stem, sample


def _default_output_dir(eval_path: Path) -> Path:
    return eval_path.parent / (eval_path.stem + "_plaintext")


def _extract_eval_file(
    eval_path: Path,
    out_dir: Path,
    sample_ids: set[str] | None,
    *,
    write_compactions: bool,
    write_messages: bool,
) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)

    scores_path = out_dir / "scores.json"
    with open(scores_path, "w") as f:
        _write_eval_scores_json(eval_path, f)
    print(f"eval: {scores_path.stat().st_size:,} bytes -> {scores_path}", file=sys.stderr)

    for stem, sample in _iter_samples(eval_path, sample_ids):
        sample_dir = out_dir / stem
        sample_dir.mkdir(parents=True, exist_ok=True)

        def write(name: str, writer) -> None:
            path = sample_dir / name
            with open(path, "w") as f:
                writer(f)
            print(f"{stem}: {path.stat().st_size:,} bytes -> {path}", file=sys.stderr)

        write("info.json", lambda f: _write_info(sample, f))

        messages = main_loop_messages(sample) if (write_messages or write_compactions) else []

        if write_compactions:
            write("compactions.txt", lambda f: _write_compactions(messages, f))
        if write_messages:
            write("messages.txt", lambda f: _write_transcript(messages, f))

        write("scores.txt", lambda f: _write_scores(sample, f))
        write("scores.json", lambda f: _write_scores_json(sample, f))

        submission = _proof_submission(sample)
        if submission is not None:
            write("submission.lean", lambda f: f.write(submission))


def main():
    parser = argparse.ArgumentParser(
        description="Extract the apn agent transcript from an Inspect .eval log into plain text."
    )
    parser.add_argument(
        "eval_files",
        nargs="+",
        help="Path(s) to .eval file(s), or a directory of .eval files",
    )
    parser.add_argument(
        "-o",
        "--output-dir",
        help=(
            "Output directory (default: <eval_stem>_plaintext next to the .eval file; "
            "with a directory or multiple eval files, each log gets its own "
            "<eval_stem>/ subdirectory here)"
        ),
    )
    parser.add_argument(
        "-s",
        "--sample",
        action="append",
        help="Extract only these sample IDs (repeatable, e.g. -s foo -s bar)",
    )
    parser.add_argument("--list-samples", action="store_true", help="List sample IDs and exit")
    mode_group = parser.add_mutually_exclusive_group()
    mode_group.add_argument(
        "--compaction-summaries",
        action="store_true",
        help="Extract only compaction summaries (condensed progress view)",
    )
    mode_group.add_argument(
        "--messages-only",
        action="store_true",
        help="Extract only full message transcripts (skip compaction summaries)",
    )
    args = parser.parse_args()

    input_paths = [Path(eval_file) for eval_file in args.eval_files]
    collection_mode = len(input_paths) > 1 or any(p.is_dir() for p in input_paths)

    eval_paths: list[Path] = []
    for input_path in input_paths:
        if input_path.is_dir():
            paths = sorted(p for p in input_path.glob("*.eval") if p.is_file())
            if not paths:
                parser.error(f"No .eval files found in {input_path}")
            eval_paths.extend(paths)
        else:
            eval_paths.append(input_path)

    if args.list_samples:
        for eval_path in eval_paths:
            for sid in list_samples(eval_path):
                print(f"{eval_path.name}: {sid}" if collection_mode else sid)
        return

    sample_ids: set[str] | None = set(args.sample) if args.sample else None
    write_compactions = not args.messages_only
    write_messages = not args.compaction_summaries

    for eval_path in eval_paths:
        if collection_mode:
            out_dir = Path(args.output_dir) / eval_path.stem if args.output_dir else _default_output_dir(eval_path)
            print(f"Extracting {eval_path} -> {out_dir}", file=sys.stderr)
        else:
            out_dir = Path(args.output_dir) if args.output_dir else _default_output_dir(eval_path)
        _extract_eval_file(
            eval_path,
            out_dir,
            sample_ids,
            write_compactions=write_compactions,
            write_messages=write_messages,
        )


if __name__ == "__main__":
    main()
