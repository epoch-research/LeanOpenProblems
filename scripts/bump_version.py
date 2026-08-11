# type: ignore
"""
Bump version in pyproject.toml, apn/__init__.py, and uv.lock.
Usage: python scripts/bump_version.py [rc|release|major|minor|patch]

The CI image tags (LeanOpenProblems_*_<version>_fc_<commit12>) are keyed on
apn.__version__ and the per-dataset FC pins (apn/data/<dataset>/fc_commit),
so bumping the version -- or changing a pin -- triggers a fresh ECR build of
the sandbox images. Keep the two version sources in lockstep -- this script
edits both.

Default is 'rc', which produces release candidate versions:
  0.1.3       -> 0.1.4rc1
  0.1.4rc1    -> 0.1.4rc2

Use 'release' to promote an RC to a final version:
  0.1.4rc2    -> 0.1.4
"""

import re
import sys
import tomllib
from pathlib import Path

# PEP 440 release candidate format: X.Y.ZrcN
VERSION_RE = re.compile(r"^(\d+)\.(\d+)\.(\d+)(?:rc(\d+))?$")

BUMP_TYPES = ("rc", "release", "major", "minor", "patch")


def parse_version(version_str: str) -> tuple[int, int, int, int | None]:
    """Parse a version string into (major, minor, patch, rc).

    rc is None for final releases, or an integer for release candidates.
    """
    match = VERSION_RE.match(version_str)
    if not match:
        raise ValueError(f"Invalid version format: {version_str}")
    major, minor, patch = int(match.group(1)), int(match.group(2)), int(match.group(3))
    rc = int(match.group(4)) if match.group(4) is not None else None
    return (major, minor, patch, rc)


def bump_version(
    version: tuple[int, int, int, int | None], bump_type: str
) -> tuple[int, int, int, int | None]:
    """Bump the version according to bump_type."""
    major, minor, patch, rc = version

    if bump_type == "rc":
        if rc is not None:
            # Already an RC: increment RC number (0.1.4rc1 -> 0.1.4rc2)
            return (major, minor, patch, rc + 1)
        else:
            # Final release: next patch as RC1 (0.1.3 -> 0.1.4rc1)
            return (major, minor, patch + 1, 1)
    elif bump_type == "release":
        if rc is None:
            raise ValueError(
                f"Cannot use 'release' on a non-RC version ({format_version(version)}). "
                "Use 'rc' first to create a release candidate."
            )
        # Promote RC to final (0.1.4rc2 -> 0.1.4)
        return (major, minor, patch, None)
    elif bump_type == "major":
        return (major + 1, 0, 0, None)
    elif bump_type == "minor":
        return (major, minor + 1, 0, None)
    elif bump_type == "patch":
        if rc is not None:
            # Promote RC to final (0.1.4rc1 -> 0.1.4)
            return (major, minor, patch, None)
        return (major, minor, patch + 1, None)
    else:
        raise ValueError(f"Invalid bump type: {bump_type}. Must be one of {BUMP_TYPES}")


def format_version(version: tuple[int, int, int, int | None]) -> str:
    """Format version tuple as a string."""
    major, minor, patch, rc = version
    base = f"{major}.{minor}.{patch}"
    if rc is not None:
        return f"{base}rc{rc}"
    return base


def update_file(file_path: Path, prefix: str, old_version: str, new_version: str) -> None:
    """Update a ``<prefix> = "<version>"`` line in a file."""
    content = file_path.read_text()

    pattern = "^" + re.escape(prefix) + r' = "' + re.escape(old_version) + r'"$'
    replacement = f'{prefix} = "{new_version}"'

    new_content = re.sub(pattern, replacement, content, flags=re.MULTILINE)

    if new_content == content:
        raise ValueError(f"Failed to update version in {file_path}")

    file_path.write_text(new_content)


def update_uv_lock(lock_path: Path, old_version: str, new_version: str) -> None:
    """Bump the project's own version in ``uv.lock``.

    uv has no command to rewrite just the version: ``uv lock`` always re-runs
    resolution (even ``--offline`` only resolves from cache), so we edit the
    lockfile directly. Only the ``apn`` package entry (``source = { editable =
    "." }``) carries the project version and nothing depends on it, so that one
    line is the entire change.

    ``tomllib`` parses the file to confirm there's exactly one ``apn`` package at
    ``old_version`` -- a structural check, not a blind pattern match. The write
    itself is a minimal text edit (no stdlib TOML *writer* exists, and a
    third-party one would reformat the whole lockfile): a regex anchored on
    ``name = "apn"`` immediately followed by its ``version`` line, uv's stable
    layout, so the diff is exactly one line and no other package is touched.
    """
    content = lock_path.read_text()

    apn_packages = [
        pkg for pkg in tomllib.loads(content).get("package", []) if pkg.get("name") == "apn"
    ]
    if len(apn_packages) != 1:
        raise ValueError(
            f"Expected exactly one 'apn' package in {lock_path}, found {len(apn_packages)}"
        )
    found_version = apn_packages[0].get("version")
    if found_version != old_version:
        raise ValueError(
            f"uv.lock has apn version {found_version!r}, expected {old_version!r}; "
            "is it in sync with pyproject.toml?"
        )

    pattern = re.compile(
        r'(?m)^(name = "apn"\nversion = ")' + re.escape(old_version) + r'(")'
    )
    new_content, n = pattern.subn(rf"\g<1>{new_version}\g<2>", content)
    if n != 1:
        raise ValueError(
            f"Failed to update apn version in {lock_path}: "
            f"expected exactly one match, found {n}"
        )

    lock_path.write_text(new_content)


def main():
    if len(sys.argv) > 2:
        print(
            f"Usage: python scripts/bump_version.py [{' | '.join(BUMP_TYPES)}]",
            file=sys.stderr,
        )
        sys.exit(1)

    bump_type = sys.argv[1] if len(sys.argv) == 2 else "rc"

    if bump_type not in BUMP_TYPES:
        print(
            f"Error: Invalid bump type '{bump_type}'. Must be one of {BUMP_TYPES}", file=sys.stderr
        )
        sys.exit(1)

    # Paths relative to repo root
    repo_root = Path(__file__).parent.parent
    pyproject_path = repo_root / "pyproject.toml"
    init_py_path = repo_root / "apn" / "__init__.py"
    uv_lock_path = repo_root / "uv.lock"

    # Read current version from pyproject.toml
    pyproject_content = pyproject_path.read_text()
    version_match = re.search(r'^version = "([^"]+)"$', pyproject_content, re.MULTILINE)

    if not version_match:
        print("Error: Could not find version in pyproject.toml", file=sys.stderr)
        sys.exit(1)

    old_version_str = version_match.group(1)
    old_version = parse_version(old_version_str)

    # Bump version
    new_version = bump_version(old_version, bump_type)
    new_version_str = format_version(new_version)

    print(f"Bumping version: {old_version_str} -> {new_version_str}")

    # Update both files (kept in lockstep)
    update_file(pyproject_path, "version", old_version_str, new_version_str)
    print(f"Updated {pyproject_path}")

    update_file(init_py_path, "__version__", old_version_str, new_version_str)
    print(f"Updated {init_py_path}")

    update_uv_lock(uv_lock_path, old_version_str, new_version_str)
    print(f"Updated {uv_lock_path}")


if __name__ == "__main__":
    main()
