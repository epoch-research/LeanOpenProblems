#!/usr/bin/env python3
"""Download eval files for a given eval-set ID to an output directory."""

import argparse
import io
import json
import re
import shutil
import struct
import subprocess
import sys
import zipfile
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

import zstandard
from environs import Env

env = Env()
env.read_env()

PROJECT_ROOT = Path(__file__).parent.parent


def _s3_bucket() -> str:
    return env.str("HAWK_S3_BUCKET")


def _aws_profile() -> str:
    return env.str("HAWK_AWS_PROFILE")


def _hawk_command() -> str:
    found = shutil.which("hawk")
    if found is not None:
        return found

    sibling = Path(sys.executable).with_name("hawk")
    if sibling.exists():
        return str(sibling)

    return "hawk"


def _s3_list_objects(prefix: str, profile: str) -> list[dict]:
    """List objects directly under an S3 prefix (no subdirectories, single page).

    Uses delimiter='/' so only files at the prefix level are returned,
    excluding subdirectories like .buffer/. Does not paginate (1000 key limit),
    which is fine because eval-set prefixes contain very few direct files.
    """
    cmd = [
        "aws",
        "s3api",
        "list-objects-v2",
        "--bucket",
        _s3_bucket(),
        "--prefix",
        prefix,
        "--delimiter",
        "/",
        "--profile",
        profile,
        "--output",
        "json",
    ]
    result = subprocess.run(cmd, capture_output=True, text=True)
    if result.returncode != 0:
        print(f"Error listing S3 path: {result.stderr.strip()}", file=sys.stderr)
        print(
            "Make sure you're logged in: aws sso login --profile " + profile,
            file=sys.stderr,
        )
        sys.exit(1)

    data = json.loads(result.stdout)
    return data.get("Contents", [])


# Statuses the log viewer treats as a valid "winner" when deduplicating retries.
_VALID_STATUSES = ("started", "success")

_UUID_PATTERN = re.compile(r"_([^_]+?)(?:\.fast)?\.eval$")


@dataclass
class EvalFile:
    name: str
    task_id: str
    status: str | None  # eval log status, or None if the header was unreadable
    tokens: int = 0  # total model tokens used, summed across models


def _task_id_from_filename(name: str) -> str:
    """Best-effort task id from the filename, used only when the header is unreadable."""
    m = _UUID_PATTERN.search(name)
    return m.group(1) if m else name


def _read_eval_header_dict(fileobj: io.BufferedIOBase) -> dict:
    """Parse header.json out of an inspect .eval file (a zstd-compressed zip).

    Reads only the header entry via seeks, so it works on a remote seekable file
    object (e.g. one returned by s3fs) without downloading the whole archive.
    """
    z = zipfile.ZipFile(fileobj)
    info = z.getinfo("header.json")
    fileobj.seek(info.header_offset)
    local = fileobj.read(30)
    name_len = struct.unpack("<H", local[26:28])[0]
    extra_len = struct.unpack("<H", local[28:30])[0]
    fileobj.seek(info.header_offset + 30 + name_len + extra_len)
    raw = fileobj.read(info.compress_size)
    if info.compress_type == zipfile.ZIP_STORED:
        data = raw
    else:
        data = zstandard.ZstdDecompressor().stream_reader(io.BytesIO(raw)).read()
    return json.loads(data)


def _eval_file_from_fileobj(name: str, open_fileobj) -> EvalFile:
    """Build an EvalFile by reading the header via open_fileobj() (a context manager)."""
    try:
        with open_fileobj() as fileobj:
            header = _read_eval_header_dict(fileobj)
        status = header.get("status")
        task_id = header.get("eval", {}).get("task_id") or _task_id_from_filename(name)
        model_usage = (header.get("stats") or {}).get("model_usage") or {}
        tokens = sum(usage.get("total_tokens", 0) for usage in model_usage.values())
    except Exception as exc:  # noqa: BLE001 - a broken/incomplete log must not abort the run
        print(f"  Warning: could not read header from {name}: {exc}", file=sys.stderr)
        status = None
        task_id = _task_id_from_filename(name)
        tokens = 0
    return EvalFile(name=name, task_id=task_id, status=status, tokens=tokens)


def _eval_file_for_local(path: Path) -> EvalFile:
    return _eval_file_from_fileobj(path.name, lambda: path.open("rb"))


def _eval_file_for_s3(fs, bucket: str, key: str) -> EvalFile:
    return _eval_file_from_fileobj(Path(key).name, lambda: fs.open(f"{bucket}/{key}", "rb"))


def _select_eval_excludes(
    files: list[EvalFile],
    *,
    force_most_tokens_on_all_error: bool = False,
) -> list[str]:
    """Return names of .eval files to exclude, keeping the viewer's "winner" per task.

    Mirrors the log viewer's "show retried logs" toggle: group logs by task id and
    keep the one whose status is started/success, breaking ties by descending
    filename. Exits with an error if any task group has no started/success log, since
    there is then no correct file to keep.
    """
    by_task: dict[str, list[EvalFile]] = defaultdict(list)
    for f in files:
        by_task[f.task_id].append(f)

    excludes: list[str] = []
    for task_id, group in by_task.items():
        # Winner ranks last: prefer started/success, then newest filename.
        ranked = sorted(group, key=lambda f: (f.status in _VALID_STATUSES, f.name))
        winner = ranked[-1]
        if winner.status not in _VALID_STATUSES:
            if force_most_tokens_on_all_error:
                ranked = sorted(group, key=lambda f: (f.tokens, f.name))
                winner = ranked[-1]
                statuses = ", ".join(
                    f"{f.name} (status={f.status}, tokens={f.tokens})" for f in group
                )
                print(
                    f"  Warning: task {task_id} has no started/success .eval file; "
                    f"force-keeping candidate with most tokens {winner.name}. "
                    f"Candidates: {statuses}",
                    file=sys.stderr,
                )
                for f in ranked[:-1]:
                    excludes.append(f.name)
                print(
                    f"Task {task_id}: keeping {winner.name} "
                    f"(status={winner.status}, force-most-tokens), "
                    f"excluding {len(group) - 1} other file(s)"
                )
                continue

            statuses = ", ".join(f"{f.name} (status={f.status})" for f in group)
            print(
                f"Error: task {task_id} has no started/success .eval file; "
                f"cannot determine which to keep. Candidates: {statuses}",
                file=sys.stderr,
            )
            sys.exit(1)
        if winner.status == "started":
            print(
                f"  Warning: keeping {winner.name} but its status is 'started' "
                f"(the run is incomplete); no success log exists for task {task_id}.",
                file=sys.stderr,
            )
        for f in ranked[:-1]:
            excludes.append(f.name)
        print(
            f"Task {task_id}: keeping {winner.name} (status={winner.status}), "
            f"excluding {len(group) - 1} other file(s)"
        )

    return excludes


def _delete_local_excludes(dest_dir: Path, excludes: list[str]) -> None:
    if not excludes:
        return

    print(f"\nDeleting {len(excludes)} outdated local .eval file(s):")
    for key in excludes:
        path = dest_dir / Path(key).name
        print(f"  {path.name}")
        path.unlink(missing_ok=True)


def _s3_list_objects_recursive(prefix: str, profile: str) -> list[dict]:
    """List all objects under an S3 prefix recursively (paginated)."""
    cmd = [
        "aws",
        "s3api",
        "list-objects-v2",
        "--bucket",
        _s3_bucket(),
        "--prefix",
        prefix,
        "--profile",
        profile,
        "--output",
        "json",
    ]
    all_objects: list[dict] = []
    continuation_token = None

    while True:
        page_cmd = list(cmd)
        if continuation_token:
            page_cmd += ["--continuation-token", continuation_token]

        result = subprocess.run(page_cmd, capture_output=True, text=True)
        if result.returncode != 0:
            print(f"Error listing S3 path: {result.stderr.strip()}", file=sys.stderr)
            sys.exit(1)

        data = json.loads(result.stdout)
        all_objects.extend(data.get("Contents", []))

        if data.get("IsTruncated"):
            continuation_token = data["NextContinuationToken"]
        else:
            break

    return all_objects


def _compute_artifact_excludes(eval_prefix: str, max_per_sample: int, profile: str) -> list[str]:
    """Return relative paths of artifact files to exclude, keeping only the N most recent per sample.

    The artifact layout is: {eval_prefix}artifacts/{sample_uuid}/scored_cases_{idx}.jsonl
    We group files by sample UUID, sort by LastModified descending, and exclude all but
    the top N per sample.
    """
    artifact_prefix = f"{eval_prefix}artifacts/"
    print(f"Listing artifacts at s3://{_s3_bucket()}/{artifact_prefix} ...")
    objects = _s3_list_objects_recursive(artifact_prefix, profile)

    if not objects:
        return []

    # Group by sample UUID (the directory immediately under artifacts/)
    by_sample: dict[str, list[tuple[str, str]]] = defaultdict(list)
    for obj in objects:
        key = obj["Key"]
        # key looks like: evals/{eval-set-id}/artifacts/{uuid}/scored_cases_00000.jsonl
        rel = key[len(artifact_prefix) :]  # {uuid}/scored_cases_00000.jsonl
        parts = rel.split("/", 1)
        if len(parts) != 2:
            continue
        sample_uuid = parts[0]
        by_sample[sample_uuid].append((obj["LastModified"], rel))

    excludes: list[str] = []
    for sample_uuid, entries in by_sample.items():
        if len(entries) <= max_per_sample:
            continue
        # Sort by modification time, most recent first
        entries.sort(key=lambda e: e[0], reverse=True)
        kept = entries[:max_per_sample]
        excluded = entries[max_per_sample:]
        for _, rel_path in excluded:
            excludes.append(f"artifacts/{rel_path}")
        print(
            f"Sample {sample_uuid}: keeping {len(kept)} most recent artifact(s), "
            f"excluding {len(excluded)}"
        )

    return excludes


def _extract_plaintext(dest_dir: Path) -> None:
    script_path = PROJECT_ROOT / "scripts" / "extract_plaintext.py"
    cmd = [sys.executable, str(script_path), str(dest_dir), "--parallel-samples"]
    print(f"\nExtracting plaintext from .eval files in {dest_dir} ...")
    result = subprocess.run(cmd)
    if result.returncode != 0:
        print("Plaintext extraction failed.", file=sys.stderr)
        sys.exit(1)


def _download_with_hawk(
    eval_set_id: str,
    dest_dir: Path,
    *,
    dry_run: bool,
) -> None:
    cmd = [_hawk_command(), "download", eval_set_id]
    if dry_run:
        cmd.append("--list")
    else:
        cmd.extend(["--output-dir", str(dest_dir)])

    print(f"\n{'Dry run: listing' if dry_run else 'Downloading'} via hawk download ...", flush=True)
    result = subprocess.run(cmd)
    if result.returncode != 0:
        print("hawk download failed.", file=sys.stderr)
        sys.exit(result.returncode)


def _download_with_s3(
    *,
    s3_uri: str,
    dest_dir: Path,
    eval_excludes: list[str],
    artifact_excludes: list[str],
    artifacts: int | None,
    dry_run: bool,
    profile: str,
) -> None:
    sync_cmd = [
        "aws",
        "s3",
        "sync",
        s3_uri,
        str(dest_dir),
        "--profile",
        profile,
        "--exclude",
        ".buffer/*",
    ]
    if artifacts is None:
        sync_cmd += ["--exclude", "artifacts/*"]
    for key in eval_excludes:
        sync_cmd += ["--exclude", Path(key).name]
    for rel_path in artifact_excludes:
        sync_cmd += ["--exclude", rel_path]
    if dry_run:
        sync_cmd.append("--dryrun")

    print(f"\n{'Dry run: ' if dry_run else ''}Downloading to {dest_dir} ...")
    result = subprocess.run(sync_cmd)
    if result.returncode != 0:
        print("Download failed.", file=sys.stderr)
        sys.exit(1)


def main():
    parser = argparse.ArgumentParser(description="Download eval files for an eval-set ID.")
    parser.add_argument(
        "eval_set_id", help="The eval-set ID (e.g. wren-compaction-01-8lp44dm72h07a9k3)"
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Show what would be downloaded without downloading.",
    )
    parser.add_argument(
        "--artifacts",
        type=int,
        default=None,
        metavar="N",
        help=(
            "Download artifacts. Omit to skip artifacts entirely. "
            "Use 0 or -1 to download all artifacts. "
            "Use a positive integer N to download only the N most recent "
            "artifact files per sample."
        ),
    )
    parser.add_argument(
        "--output-root",
        default=str(PROJECT_ROOT / "logs"),
        help="Directory under which <eval-set-id>/ will be created.",
    )
    parser.add_argument(
        "--method",
        choices=("hawk", "s3"),
        default="s3",
        help=(
            "Download method. 'hawk' uses the Hawk API and presigned URLs; "
            "'s3' uses aws s3 sync against HAWK_S3_BUCKET."
        ),
    )
    parser.add_argument(
        "--plaintext",
        action="store_true",
        help="After downloading, extract plaintext for all .eval files in the destination directory.",
    )
    parser.add_argument(
        "--all",
        action="store_true",
        help="Download all .eval files, including superseded retries for the same task.",
    )
    parser.add_argument(
        "--force-most-tokens-on-all-error",
        action="store_true",
        help=(
            "If every retry for a task is status=error/unreadable, keep the .eval that "
            "used the most tokens instead of failing. Use only for intentional recovery "
            "of broken eval-sets."
        ),
    )
    args = parser.parse_args()

    if args.method == "hawk" and args.artifacts is not None:
        print(
            "--artifacts is only supported with --method s3; hawk download only downloads .eval files.",
            file=sys.stderr,
        )
        sys.exit(1)

    output_root = Path(args.output_root)
    if not output_root.is_absolute():
        output_root = PROJECT_ROOT / output_root
    dest_dir = output_root / args.eval_set_id
    dest_dir.mkdir(parents=True, exist_ok=True)

    if args.method == "hawk":
        _download_with_hawk(args.eval_set_id, dest_dir, dry_run=args.dry_run)

        if not args.dry_run and not args.all:
            files = [_eval_file_for_local(p) for p in sorted(dest_dir.glob("*.eval"))]
            eval_excludes = _select_eval_excludes(files)
            _delete_local_excludes(dest_dir, eval_excludes)

    else:
        profile = _aws_profile()
        s3_prefix = f"evals/{args.eval_set_id}/"
        s3_uri = f"s3://{_s3_bucket()}/{s3_prefix}"

        print(f"Listing files at {s3_uri} ...")
        objects = _s3_list_objects(s3_prefix, profile)

        if not objects:
            print(f"No files found at {s3_uri}", file=sys.stderr)
            sys.exit(1)

        print(f"Found {len(objects)} file(s):")
        for obj in objects:
            name = Path(obj["Key"]).name
            size = obj["Size"]
            modified = obj["LastModified"]
            print(f"  {modified}  {size:>12}  {name}")

        # Deduplicate retries: keep the started/success .eval per task (viewer logic).
        eval_excludes = []
        if not args.all:
            import s3fs  # type: ignore[import-untyped]

            fs = s3fs.S3FileSystem(profile=profile)
            eval_objects = [obj for obj in objects if obj["Key"].endswith(".eval")]
            files = [_eval_file_for_s3(fs, _s3_bucket(), obj["Key"]) for obj in eval_objects]
            eval_excludes = _select_eval_excludes(
                files,
                force_most_tokens_on_all_error=args.force_most_tokens_on_all_error,
            )

        if eval_excludes:
            print(f"\nExcluding {len(eval_excludes)} superseded .eval file(s):")
            for name in eval_excludes:
                print(f"  {name}")

        # Determine which artifact files to exclude
        artifact_excludes: list[str] = []
        if args.artifacts is not None and args.artifacts > 0:
            artifact_excludes = _compute_artifact_excludes(s3_prefix, args.artifacts, profile)

        _download_with_s3(
            s3_uri=s3_uri,
            dest_dir=dest_dir,
            eval_excludes=eval_excludes,
            artifact_excludes=artifact_excludes,
            artifacts=args.artifacts,
            dry_run=args.dry_run,
            profile=profile,
        )

    if not args.dry_run:
        print(f"Done. Files saved to {dest_dir}")
        if args.plaintext:
            _extract_plaintext(dest_dir)
    elif args.plaintext:
        print("Dry run: skipping plaintext extraction.")


if __name__ == "__main__":
    main()
