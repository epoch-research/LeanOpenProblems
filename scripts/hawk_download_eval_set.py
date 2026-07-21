#!/usr/bin/env python3
"""Download eval files for a given eval-set ID from S3 to ./logs/<eval-set-id>/."""

import argparse
import json
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

from environs import Env

env = Env()
env.read_env()

PROJECT_ROOT = Path(__file__).parent.parent

S3_BUCKET = env.str("HAWK_S3_BUCKET")
S3_URI = f"s3://{S3_BUCKET}"
AWS_PROFILE = env.str("HAWK_AWS_PROFILE")


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
        S3_BUCKET,
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


def _compute_eval_excludes(
    objects: list[dict],
    force_newest: bool = False,
    force_largest: bool = False,
) -> list[str]:
    """Return keys of outdated .eval files to exclude from download.

    Groups .eval files by UUID. For each UUID with multiple files, keeps only
    the one that is both the newest and the largest. Raises if those disagree
    (unless force_newest or force_largest is set).
    """
    uuid_pattern = re.compile(r"_([^_]+?)(?:\.fast)?\.eval$")

    # Group by UUID: list of (LastModified, Size, Key)
    by_uuid: dict[str, list[tuple[str, int, str]]] = defaultdict(list)

    for obj in objects:
        key = obj["Key"]
        if not key.endswith(".eval"):
            continue
        m = uuid_pattern.search(key)
        if not m:
            continue
        uuid = m.group(1)
        by_uuid[uuid].append((obj["LastModified"], obj["Size"], key))

    excludes: list[str] = []
    for uuid, entries in by_uuid.items():
        # Prefer .fast.eval over regular .eval for the same UUID
        fast_entries = [e for e in entries if e[2].endswith(".fast.eval")]
        regular_entries = [e for e in entries if not e[2].endswith(".fast.eval")]

        if fast_entries and regular_entries:
            # Exclude all regular .eval files when .fast.eval exists
            for _, _, key in regular_entries:
                excludes.append(key)
            print(
                f"UUID {uuid}: preferring .fast.eval, excluding {len(regular_entries)} regular .eval file(s)"
            )
            # Continue dedup within fast_entries only
            entries = fast_entries

        if len(entries) <= 1:
            continue
        newest = max(entries, key=lambda e: e[0])
        largest = max(entries, key=lambda e: e[1])
        if newest[2] != largest[2]:
            if force_newest:
                keep = newest[2]
                print(
                    f"UUID {uuid}: newest ({Path(newest[2]).name}) != largest ({Path(largest[2]).name}); forcing newest"
                )
            elif force_largest:
                keep = largest[2]
                print(
                    f"UUID {uuid}: newest ({Path(newest[2]).name}) != largest ({Path(largest[2]).name}); forcing largest"
                )
            else:
                print(
                    f"Error: for UUID {uuid}, newest file ({newest[2]}) "
                    f"differs from largest file ({largest[2]}). "
                    f"Cannot determine which to keep. "
                    f"Use --force-newest, --force-largest, or --all to resolve.",
                    file=sys.stderr,
                )
                sys.exit(1)
        else:
            keep = newest[2]
        for _, _, key in entries:
            if key != keep:
                excludes.append(key)
        print(f"UUID {uuid}: keeping {Path(keep).name}, excluding {len(entries) - 1} older file(s)")

    return excludes


def _s3_list_objects_recursive(prefix: str, profile: str) -> list[dict]:
    """List all objects under an S3 prefix recursively (paginated)."""
    cmd = [
        "aws",
        "s3api",
        "list-objects-v2",
        "--bucket",
        S3_BUCKET,
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
    print(f"Listing artifacts at s3://{S3_BUCKET}/{artifact_prefix} ...")
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


def main():
    parser = argparse.ArgumentParser(description="Download eval files for an eval-set ID from S3.")
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
        "--plaintext",
        action="store_true",
        help="After downloading, extract plaintext for all .eval files in the destination directory.",
    )
    dedup_group = parser.add_mutually_exclusive_group()
    dedup_group.add_argument(
        "--all",
        action="store_true",
        help="Download all .eval files, even duplicates with the same UUID.",
    )
    dedup_group.add_argument(
        "--force-newest",
        action="store_true",
        help="When newest and largest .eval files for a UUID disagree, keep the newest.",
    )
    dedup_group.add_argument(
        "--force-largest",
        action="store_true",
        help="When newest and largest .eval files for a UUID disagree, keep the largest.",
    )
    args = parser.parse_args()

    s3_prefix = f"evals/{args.eval_set_id}/"
    s3_uri = f"{S3_URI}/{s3_prefix}"
    dest_dir = PROJECT_ROOT / "logs" / args.eval_set_id
    dest_dir.mkdir(parents=True, exist_ok=True)

    print(f"Listing files at {s3_uri} ...")
    objects = _s3_list_objects(s3_prefix, AWS_PROFILE)

    if not objects:
        print(f"No files found at {s3_uri}", file=sys.stderr)
        sys.exit(1)

    print(f"Found {len(objects)} file(s):")
    for obj in objects:
        name = Path(obj["Key"]).name
        size = obj["Size"]
        modified = obj["LastModified"]
        print(f"  {modified}  {size:>12}  {name}")

    # One-per-UUID mode: deduplicate .eval files sharing the same UUID
    eval_excludes: list[str] = []
    if not args.all:
        eval_excludes = _compute_eval_excludes(
            objects,
            force_newest=args.force_newest,
            force_largest=args.force_largest,
        )

    if eval_excludes:
        print(f"\nExcluding {len(eval_excludes)} outdated .eval file(s):")
        for key in eval_excludes:
            print(f"  {Path(key).name}")

    # Determine which artifact files to exclude
    artifact_excludes: list[str] = []

    if args.artifacts is not None and args.artifacts > 0:
        artifact_excludes = _compute_artifact_excludes(s3_prefix, args.artifacts, AWS_PROFILE)

    # Download using s3 sync
    sync_cmd = [
        "aws",
        "s3",
        "sync",
        s3_uri,
        str(dest_dir),
        "--profile",
        AWS_PROFILE,
        "--exclude",
        ".buffer/*",
    ]
    if args.artifacts is None:
        sync_cmd += ["--exclude", "artifacts/*"]
    for key in eval_excludes:
        sync_cmd += ["--exclude", Path(key).name]
    for rel_path in artifact_excludes:
        sync_cmd += ["--exclude", rel_path]
    if args.dry_run:
        sync_cmd.append("--dryrun")
    print(f"\n{'Dry run: ' if args.dry_run else ''}Downloading to {dest_dir} ...")
    result = subprocess.run(sync_cmd)

    if result.returncode != 0:
        print("Download failed.", file=sys.stderr)
        sys.exit(1)

    if not args.dry_run:
        print(f"Done. Files saved to {dest_dir}")
        if args.plaintext:
            _extract_plaintext(dest_dir)
    elif args.plaintext:
        print("Dry run: skipping plaintext extraction.")


if __name__ == "__main__":
    main()
