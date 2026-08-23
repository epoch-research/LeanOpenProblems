#!/usr/bin/env python3
"""Populate LeanOpenProblems-results from selected plaintext runs.

The export is additive: destination-only files are retained. Agent transcripts
and operating-system metadata are omitted.
"""

from __future__ import annotations

import argparse
import os
import shutil
import stat
from dataclasses import dataclass
from pathlib import Path


EXCLUDED_NAMES = frozenset({".DS_Store", "messages.txt", "compactions.txt"})
DEFAULT_DEST = Path(
    "/Users/t/repos/github.com/epoch-research/LeanOpenProblems-results"
)
CHUNK_SIZE = 1024 * 1024


@dataclass
class SyncStats:
    files: int = 0
    symlinks: int = 0
    changes: int = 0


def same_file_contents(left: Path, right: Path) -> bool:
    """Return whether two regular files contain identical bytes."""
    if left.stat().st_size != right.stat().st_size:
        return False
    with left.open("rb") as left_file, right.open("rb") as right_file:
        while left_chunk := left_file.read(CHUNK_SIZE):
            if left_chunk != right_file.read(CHUNK_SIZE):
                return False
        return right_file.read(1) == b""


def same_mode(left: Path, right: Path) -> bool:
    return stat.S_IMODE(left.stat().st_mode) == stat.S_IMODE(right.stat().st_mode)


def path_exists(path: Path) -> bool:
    """Like Path.exists(), but true for a broken symlink."""
    return os.path.lexists(path)


def sync_file(source: Path, target: Path, *, dry_run: bool) -> bool:
    """Copy one regular file if its contents or mode differ."""
    target_is_regular = (
        path_exists(target) and not target.is_symlink() and target.is_file()
    )
    contents_match = target_is_regular and same_file_contents(source, target)
    mode_matches = target_is_regular and same_mode(source, target)
    if contents_match and mode_matches:
        return False
    if dry_run:
        return True
    if path_exists(target) and not target_is_regular:
        if target.is_dir() and not target.is_symlink():
            raise RuntimeError(
                f"cannot replace destination directory with file: {target}"
            )
        target.unlink()
    target.parent.mkdir(parents=True, exist_ok=True)
    if contents_match:
        shutil.copymode(source, target)
    else:
        shutil.copyfile(source, target)
        shutil.copymode(source, target)
    return True


def sync_symlink(source: Path, target: Path, *, dry_run: bool) -> bool:
    """Copy one symlink without following it."""
    link_target = os.readlink(source)
    if target.is_symlink() and os.readlink(target) == link_target:
        return False
    if dry_run:
        return True
    if path_exists(target):
        if target.is_dir() and not target.is_symlink():
            raise RuntimeError(
                f"cannot replace destination directory with symlink: {target}"
            )
        target.unlink()
    target.parent.mkdir(parents=True, exist_ok=True)
    target.symlink_to(link_target, target_is_directory=source.is_dir())
    return True


def sync_tree(source: Path, target: Path, *, dry_run: bool) -> SyncStats:
    """Add or update source entries under target, retaining target-only entries."""
    stats = SyncStats()
    for current, directory_names, file_names in os.walk(source, followlinks=False):
        current_path = Path(current)
        directory_names[:] = sorted(
            name for name in directory_names if name not in EXCLUDED_NAMES
        )
        file_names = sorted(name for name in file_names if name not in EXCLUDED_NAMES)

        relative = current_path.relative_to(source)
        target_directory = target / relative
        if path_exists(target_directory) and not target_directory.is_dir():
            raise RuntimeError(
                f"destination directory is not a directory: {target_directory}"
            )
        if not dry_run:
            target_directory.mkdir(parents=True, exist_ok=True)

        symlink_directories = [
            name for name in directory_names if (current_path / name).is_symlink()
        ]
        directory_names[:] = [
            name for name in directory_names if name not in symlink_directories
        ]
        for name in symlink_directories:
            stats.symlinks += 1
            if sync_symlink(
                current_path / name, target_directory / name, dry_run=dry_run
            ):
                stats.changes += 1

        for name in file_names:
            source_file = current_path / name
            target_file = target_directory / name
            if source_file.is_symlink():
                stats.symlinks += 1
                changed = sync_symlink(source_file, target_file, dry_run=dry_run)
            else:
                stats.files += 1
                changed = sync_file(source_file, target_file, dry_run=dry_run)
            if changed:
                stats.changes += 1
    return stats


def plaintext_directory(logs_dir: Path, run: str) -> Path:
    matches = sorted(
        path for path in (logs_dir / run).glob("*_plaintext") if path.is_dir()
    )
    if len(matches) != 1:
        raise RuntimeError(
            f"expected exactly one *_plaintext directory for {run}; found {len(matches)}"
        )
    return matches[0]


def parse_args() -> argparse.Namespace:
    repo_root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "runs",
        nargs="+",
        metavar="RUN",
        help="run directory name under the logs directory (repeatable)",
    )
    parser.add_argument(
        "--dest",
        type=Path,
        default=DEFAULT_DEST,
        help=f"results repository (default: {DEFAULT_DEST})",
    )
    parser.add_argument(
        "--logs-dir",
        type=Path,
        default=repo_root / "logs",
        help="source logs directory (default: <repository>/logs)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="compare source and destination without writing files",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    for run in args.runs:
        source = plaintext_directory(args.logs_dir, run)
        target = args.dest / "runs" / run
        stats = sync_tree(source, target, dry_run=args.dry_run)
        prefix = "would change" if args.dry_run else "changed"
        print(
            f"{run}: {stats.files} files, {stats.symlinks} symlinks, "
            f"{prefix} {stats.changes}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
