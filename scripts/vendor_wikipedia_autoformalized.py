# type: ignore
"""Vendor the Wikipedia-autoformalized sources from a downloaded run of our
autoformalization pipeline (``epoch-research/autoformalization``).

Input: a Hawk eval-set download directory holding the run's single Inspect
``.eval`` log next to its per-sample ``artifacts/<sample uuid>/`` sidecars
(``hawk download-artifacts <eval-set-id> -o logs/<eval-set-id>/artifacts``).

Selection (``scripts/wikipedia_autoformalized_isolation.py``): a sample's
final file is vendored iff its headline ``formalized`` score is CORRECT or
PARTIAL -- the adjudicator accepted a compiling final file that survived the
settle probe, stating every (C) or some (P) of the decomposed sub-questions --
and the adjudicator's ``final_file_confidence`` (P(the file faithfully
formalizes every slot it states)) is at least ``MIN_CONFIDENCE``. A selected
file that imports a sibling FC problem module is *not* vendored: the sandbox
images carry only the FC proving library, so it cannot elaborate there. Every
decision is recorded in the run table.

Output, all under ``apn/data/wikipedia_autoformalized/``:

    Sources/<Name>.lean         the vendored final files, verbatim bytes, named
                                by the run's FC file convention (the basename of
                                the sample's ``conventions.fc_path``)
    fc_commit                   the FC pin every sample of the run compiled against
    metadata/run_samples.jsonl  one row per run sample, selected or not
    metadata/run.json           run identity, selection rule and counts

This is a *vendor-time* dev tool (it needs ``inspect_ai`` to read the log).
Then run ``scripts/generate_wikipedia_autoformalized_isolated.py``.

    uv run python scripts/vendor_wikipedia_autoformalized.py \\
        --run-dir ~/repos/github.com/epoch-research/autoformalization/logs/autoformalize-full-r8zuxgce3jf7ppre
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import zipfile
from collections import Counter
from pathlib import Path

from inspect_ai.log import read_eval_log, read_eval_log_sample_summaries

from apn.dataset import fc_profile
from scripts.fc_statements import strip_comments
from scripts.wikipedia_autoformalized_isolation import (
    ACCEPTED_FORMALIZED,
    MIN_CONFIDENCE,
    RUN_INFO_PATH,
    RUN_SAMPLES_PATH,
    SIBLING_IMPORT_REASON,
    SOURCES_DIR,
    WIKIPEDIA_AUTOFORMALIZED_DIR,
    RunSample,
    is_selected,
    sibling_imports,
    write_run_samples,
)

REQUIRED_ARTIFACTS = ("final.lean", "decision.json", "result.json")


def read_run(log_path: Path) -> tuple[dict, list[dict]]:
    """The log header facts and one record per sample: the headline score and
    result dict from the sample summaries, the full metadata (naming
    conventions, title, FC pin) from the sample's JSON inside the .eval zip
    (summaries truncate large metadata fields)."""
    header = read_eval_log(str(log_path), header_only=True)
    summaries = read_eval_log_sample_summaries(str(log_path))
    # The log is a multi-frame zstd zip; inspect's patch makes zipfile read it.
    from inspect_ai._util.zipfile import _install_multiframe_patches

    _install_multiframe_patches()
    samples: list[dict] = []
    with zipfile.ZipFile(log_path) as zf:
        for s in summaries:
            full = json.loads(zf.read(f"samples/{s.id}_epoch_{s.epoch}.json"))
            if full["uuid"] != s.uuid:
                raise SystemExit(f"{s.id}: summary uuid {s.uuid} != sample uuid {full['uuid']}")
            score = (s.scores or {}).get("formalized")
            samples.append(
                {
                    "id": str(s.id),
                    "uuid": s.uuid,
                    "formalized": score.value if score else None,
                    "result": (s.metadata or {}).get("result") or {},
                    "metadata": full["metadata"],
                    "error": str(getattr(s.error, "message", s.error)) if s.error else None,
                }
            )
    info = {
        "eval_set_id": getattr(header.eval, "eval_set_id", None) or log_path.parent.name,
        "log": log_path.name,
        "run_id": header.eval.run_id,
        "task": header.eval.task,
        "model": header.eval.model,
        "task_args": dict(header.eval.task_args or {}),
        "created": header.eval.created,
        "status": header.status,
    }
    return info, samples


def _theorem_declared_once(code: str, name: str) -> bool:
    pat = re.compile(
        r"(?m)^(?:(?:private|protected|nonrec)\s+)*(?:theorem|lemma)\s+"
        + re.escape(name)
        + r"(?![\w'.!?])"
    )
    return len(pat.findall(code)) == 1


def main() -> None:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument(
        "--run-dir",
        required=True,
        type=Path,
        help="eval-set download dir: the .eval log + artifacts/<uuid>/ sidecars",
    )
    args = ap.parse_args()

    logs = sorted(args.run_dir.glob("*.eval"))
    if len(logs) != 1:
        raise SystemExit(f"expected exactly one .eval log in {args.run_dir}, found {logs}")
    artifacts_dir = args.run_dir / "artifacts"
    if not artifacts_dir.is_dir():
        raise SystemExit(f"no artifacts/ directory in {args.run_dir}")

    info, samples = read_run(logs[0])
    print(f"Read {len(samples)} samples from {logs[0].name} (status {info['status']})")

    pins = {s["metadata"]["fc_commit"] for s in samples}
    if len(pins) != 1:
        raise SystemExit(f"samples compiled against several FC pins: {sorted(pins)}")
    (pin,) = pins
    util_module = fc_profile(pin).util_module  # fails loudly on an unregistered pin

    SOURCES_DIR.mkdir(parents=True, exist_ok=True)
    for old in SOURCES_DIR.glob("*.lean"):
        old.unlink()

    rows: list[RunSample] = []
    filenames_casefolded: dict[str, str] = {}
    not_vendored: list[tuple[str, str]] = []
    n_kept_vendored = 0
    for smp in sorted(samples, key=lambda s: s["id"]):
        md = smp["metadata"]
        conv = md["conventions"]
        result = smp["result"]
        confidence = result.get("final_file_confidence")
        selected = is_selected(smp["formalized"], confidence)
        art = artifacts_dir / smp["uuid"]
        decision = (
            json.loads((art / "decision.json").read_text())
            if (art / "decision.json").is_file()
            else None
        )
        probe = result.get("probe") or {}
        row = {
            "problem_id": smp["id"],
            "title": md["title"],
            "reference_url": conv["reference_url"],
            "uuid": smp["uuid"],
            "lean_namespace": conv["lean_namespace"],
            "decision": result.get("decision"),
            "formalized": smp["formalized"],
            "adjudicator_confidence": confidence,
            "slots_kept": result.get("slots_kept"),
            "slots_total": result.get("slots_total"),
            "kept_slots": decision.get("kept_slots") if decision else None,
            "probe_claim": probe.get("claim"),
            "probe_verified": probe.get("verified"),
            "error": smp["error"],
            "selected": selected,
            "source": None,
            "not_vendored_reason": None,
        }
        if selected:
            missing = [n for n in REQUIRED_ARTIFACTS if not (art / n).is_file()]
            if missing:
                raise SystemExit(
                    f"{smp['id']}: missing artifacts {missing} (uuid {smp['uuid']}); "
                    f"re-run hawk download-artifacts"
                )
            if json.loads((art / "result.json").read_text()) != result:
                raise SystemExit(f"{smp['id']}: artifacts result.json != the log's metadata.result")
            kept = row["kept_slots"]
            if not kept or len(kept) != result.get("slots_kept"):
                raise SystemExit(
                    f"{smp['id']}: kept_slots {kept} inconsistent with slots_kept={result.get('slots_kept')}"
                )
            raw = (art / "final.lean").read_bytes()
            text = raw.decode("utf-8")
            code = strip_comments(text)
            for slot in kept:
                if not _theorem_declared_once(code, slot):
                    raise SystemExit(f"{smp['id']}: kept slot {slot!r} is not declared exactly once")
            siblings = sibling_imports(text, util_module)
            if siblings:
                row["not_vendored_reason"] = SIBLING_IMPORT_REASON.format(modules=", ".join(siblings))
                not_vendored.append((smp["id"], row["not_vendored_reason"]))
            else:
                filename = Path(conv["fc_path"]).name
                if not re.fullmatch(r"[A-Za-z0-9_]+\.lean", filename):
                    raise SystemExit(f"{smp['id']}: unexpected source filename {filename!r}")
                if filename.casefold() in filenames_casefolded:
                    raise SystemExit(
                        f"{smp['id']}: source filename {filename} collides (casefolded) with "
                        f"{filenames_casefolded[filename.casefold()]}"
                    )
                filenames_casefolded[filename.casefold()] = smp["id"]
                (SOURCES_DIR / filename).write_bytes(raw)
                row["source"] = f"Sources/{filename}"
                n_kept_vendored += len(kept)
        rows.append(RunSample(**row))

    (WIKIPEDIA_AUTOFORMALIZED_DIR / "fc_commit").write_text(pin + "\n")
    write_run_samples(rows)
    formalized_counts = Counter(str(r.formalized) for r in rows)
    n_selected = sum(r.selected for r in rows)
    n_vendored = sum(r.source is not None for r in rows)
    info.update(
        {
            "fc_commit": pin,
            "selection": {
                "formalized": list(ACCEPTED_FORMALIZED),
                "min_confidence": MIN_CONFIDENCE,
            },
            "counts": {
                "samples": len(rows),
                "formalized": dict(sorted(formalized_counts.items())),
                "selected": n_selected,
                "vendored": n_vendored,
                "not_vendored": len(not_vendored),
                "kept_slots_vendored": n_kept_vendored,
            },
        }
    )
    RUN_INFO_PATH.write_text(json.dumps(info, indent=2, ensure_ascii=False) + "\n")
    print(
        f"formalized: {dict(formalized_counts)}\n"
        f"selected (C/P and confidence >= {MIN_CONFIDENCE}): {n_selected}\n"
        f"vendored: {n_vendored} files ({n_kept_vendored} kept slots) to {SOURCES_DIR}\n"
        f"not vendored: {len(not_vendored)}"
    )
    for pid, reason in not_vendored:
        print(f"  {pid}: {reason}")
    print(f"Wrote {RUN_SAMPLES_PATH}, {RUN_INFO_PATH}, fc_commit={pin[:12]}\n"
          "Next: uv run python scripts/generate_wikipedia_autoformalized_isolated.py")


if __name__ == "__main__":
    sys.exit(main())
