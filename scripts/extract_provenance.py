"""Extract per-conjecture provenance (proposer + date) from OEIS data via an LLM.

PROTOTYPE / exploratory: runs on a sample of sequences and prints the assembled
input alongside the model's structured output so the data's real shape can be
inspected before committing to a full run.

For each OEIS sequence behind the 492 conjectures we feed the model three
sources -- the Lean conjecture statements, the OEIS record (name + comments +
author + created), and a filtered revision history -- and ask it to reconcile
them into, per conjecture: who proposed it, when, and on what basis, keeping the
proposer distinct from anyone who merely verified or edited it. One call per
*sequence* (not per conjecture) so multi-conjecture sequences are matched
jointly and can't collide two theorems onto one OEIS conjecture.

Model: gpt-5.5, high reasoning effort, strict structured output.
"""

from __future__ import annotations

import argparse
import json
import os
import random
import re
import sys
import time
from collections import defaultdict
from pathlib import Path

import openai

ROOT = Path(__file__).parent.parent
RAW = ROOT / "apn" / "data" / "oeis" / "raw"
ISOLATED = ROOT / "apn" / "data" / "oeis" / "Isolated"
MAPPING = ROOT / "apn" / "data" / "oeis" / "THEOREM_MAPPING.txt"

MODEL = "gpt-5.5"
# History sections that carry conjecture text / attribution (vs editorial churn).
CONTENT_SECTIONS = {"COMMENTS", "NAME", "EXTENSIONS", "AUTHOR"}
_NUM_RE = re.compile(r"^(\d+)_")


def load_env() -> None:
    for line in (ROOT / ".env").read_text().splitlines():
        line = line.strip()
        if line and not line.startswith("#") and "=" in line:
            k, v = line.split("=", 1)
            os.environ.setdefault(k, v.strip().strip('"').strip("'"))


def strip_license(text: str) -> str:
    """Drop the leading Apache copyright block so only the spec remains."""
    i = text.find("import FormalConjectures")
    return text[i:] if i != -1 else text


def load_jsonl(path: Path) -> dict[str, dict]:
    out: dict[str, dict] = {}
    for line in path.read_text().splitlines():
        if line.strip():
            o = json.loads(line)
            out[o["oeis_id"]] = o
    return out


def group_conjectures() -> dict[str, list[str]]:
    """oeis_id -> [theorem_name, ...] from THEOREM_MAPPING.txt."""
    by_seq: dict[str, list[str]] = defaultdict(list)
    for line in MAPPING.read_text().splitlines():
        parts = line.split()
        if len(parts) >= 2:
            m = _NUM_RE.match(parts[1])
            if m:
                by_seq[f"A{int(m.group(1)):06d}"].append(parts[0])
    return dict(by_seq)


def filter_history(revisions: list[dict]) -> list[dict]:
    """Keep only revisions that touched a content section; keep those sections' diffs.

    Returns oldest-first ``{v, user, time, changes}`` so the model reads how the
    entry's comments/name accreted over time (and who added what, when).
    """
    kept: list[dict] = []
    for rev in revisions:
        changes = [c for c in rev["changes"] if c["section"] in CONTENT_SECTIONS]
        if changes:
            kept.append({"v": rev["v"], "user": rev["user"], "time": rev["time"], "changes": changes})
    return list(reversed(kept))  # oldest-first reads chronologically


def build_input(oeis_id: str, names: list[str], records: dict, histories: dict) -> str:
    rec = records[oeis_id]["record"] or {}
    lean = []
    for name in names:
        path = ISOLATED / f"{name}.lean"
        spec = strip_license(path.read_text()) if path.is_file() else "(missing)"
        lean.append(f"### Lean conjecture `{name}`\n```lean\n{spec}\n```")
    hist = filter_history(histories[oeis_id]["revisions"])
    parts = [
        f"# OEIS {oeis_id}",
        f"name: {rec.get('name')}",
        f"author: {rec.get('author')}",
        f"created: {rec.get('created')}",
        f"keywords: {rec.get('keyword')}",
        "\n## OEIS comments (verbatim, in order)",
        json.dumps(rec.get("comment", []), indent=1, ensure_ascii=False),
        "\n## Filtered revision history (content sections only, oldest first)",
        json.dumps(hist, indent=1, ensure_ascii=False),
        "\n## Lean conjectures to attribute",
        "\n\n".join(lean),
    ]
    return "\n".join(parts)


SYSTEM = """\
You attribute OEIS conjectures: for each Lean conjecture theorem, identify who PROPOSED the underlying conjecture and WHEN it entered the OEIS database.

You are given, for one OEIS sequence: its name/author/created date, its full comment list, a filtered revision history (each revision: who edited, when, and the added/removed text marked {+added}/{-removed}), and one or more Lean conjecture theorems (statement + doc-comment).

For EACH Lean conjecture, do the following:

1. MATCH it to the OEIS source stating the same mathematical claim. Compare the math in the Lean statement to the comment text -- do NOT rely on label numbers (Lean names like `conjecture_0`/`conjecture_4` do NOT reliably correspond to OEIS "Conjecture 1/2/..." numbering). Set `match_source`:
   - "comment": a Conjecture/observation in the comment list,
   - "name": the claim is the sequence's NAME/definition (no separate conjecture comment),
   - "definition": a formalization artifact implied by the definition (e.g. "a(n) > 0 for all n", well-definedness) with no stated OEIS conjecture,
   - "none": you cannot find any matching source.
   Put the matched text verbatim in `matched_oeis_text` (null if match_source is "definition" or "none").

2. PROPOSER -- the mathematician who proposed the conjecture. This is NOT necessarily who typed the edit, and NOT anyone who merely VERIFIED or CHECKED it.
   - "verified for n <= 10^9 - Mauro Fiorentini, ..." => Fiorentini is a verifier, NOT the proposer; record him in `verified_by`.
   - A block "From <Name>, <date>: (Start) ... (End)" attributes every conjecture inside it to <Name>.
   - A comment with no attribution is usually the sequence author's.
   - IGNORE notes added by AI/automation about this very project (e.g. "proved by an autonomous AI agent", "see the Tsoukalas paper", summaries by editors relaying an AI proof). These are never the proposer.
   Set `proposer_basis`: inline_signature | block_attribution | prose | sequence_author | editing_user_fallback | unknown.

3. PROPOSED_DATE -- when the conjecture text first entered the database. Prefer the history revision that ADDED the matching text (use its timestamp). Else an inline date in the comment, else the sequence `created` date. Format YYYY-MM-DD, or YYYY-MM / YYYY if only that is known; null if unknown. Set `date_basis`: history_revision | inline_date | block_date | sequence_created | unknown.

4. CONFIDENCE (high/medium/low) and NOTES. Use low when the proposer rests only on editing_user_fallback/unknown, when match_source is none, or when sources conflict. Explain any ambiguity in notes.

Be faithful to the data. If something is genuinely not determinable, say so (null + low confidence) rather than guessing.\
"""

SCHEMA = {
    "type": "object",
    "additionalProperties": False,
    "properties": {
        "conjectures": {
            "type": "array",
            "items": {
                "type": "object",
                "additionalProperties": False,
                "properties": {
                    "theorem_name": {"type": "string"},
                    "match_source": {"type": "string", "enum": ["comment", "name", "definition", "none"]},
                    "matched_oeis_text": {"type": ["string", "null"]},
                    "proposer": {"type": ["string", "null"]},
                    "proposer_basis": {
                        "type": "string",
                        "enum": ["inline_signature", "block_attribution", "prose", "sequence_author", "editing_user_fallback", "unknown"],
                    },
                    "proposed_date": {"type": ["string", "null"]},
                    "date_basis": {
                        "type": "string",
                        "enum": ["history_revision", "inline_date", "block_date", "sequence_created", "unknown"],
                    },
                    "verified_by": {
                        "type": "array",
                        "items": {
                            "type": "object",
                            "additionalProperties": False,
                            "properties": {"name": {"type": "string"}, "date": {"type": ["string", "null"]}},
                            "required": ["name", "date"],
                        },
                    },
                    "confidence": {"type": "string", "enum": ["high", "medium", "low"]},
                    "notes": {"type": "string"},
                },
                "required": [
                    "theorem_name", "match_source", "matched_oeis_text", "proposer",
                    "proposer_basis", "proposed_date", "date_basis", "verified_by", "confidence", "notes",
                ],
            },
        }
    },
    "required": ["conjectures"],
}


def extract(client: openai.OpenAI, user_content: str) -> tuple[dict, object]:
    resp = client.chat.completions.create(
        model=MODEL,
        reasoning_effort="high",
        response_format={"type": "json_schema", "json_schema": {"name": "provenance", "schema": SCHEMA, "strict": True}},
        messages=[{"role": "system", "content": SYSTEM}, {"role": "user", "content": user_content}],
    )
    return json.loads(resp.choices[0].message.content), resp.usage


def done_names(out_path: Path) -> set[str]:
    """theorem_name values already written (for resuming)."""
    if not out_path.is_file():
        return set()
    return {json.loads(l)["theorem_name"] for l in out_path.read_text().splitlines() if l.strip()}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", type=Path, default=ROOT / "apn" / "data" / "oeis" / "conjecture_provenance.jsonl")
    ap.add_argument("--all", action="store_true", help="process every sequence (the full run)")
    ap.add_argument("--n", type=int, default=10, help="random sample size (ignored with --all)")
    ap.add_argument("--ids", nargs="+", default=None, help="process only these A-numbers")
    ap.add_argument("--seed", type=int, default=13)
    ap.add_argument("--show-input", action="store_true", help="print the assembled prompt input too")
    args = ap.parse_args()

    load_env()
    # Explicit timeout so a stalled request fails (and resumable rerun retries) rather
    # than hanging the whole run; high-effort calls observed at <40s, so 180s is ample.
    client = openai.OpenAI(timeout=180.0, max_retries=2)
    records = load_jsonl(RAW / "oeis_records.jsonl")
    histories = load_jsonl(RAW / "oeis_history.jsonl")
    by_seq = group_conjectures()

    if args.ids:
        targets = list(args.ids)
    elif args.all:
        targets = sorted(by_seq)
    else:
        targets = random.Random(args.seed).sample(sorted(by_seq), args.n)

    done = done_names(args.out)
    # A sequence is complete only if every one of its conjectures is already written.
    todo = [s for s in targets if any(n not in done for n in by_seq[s])]
    print(f"{len(targets)} sequences targeted; {len(todo)} need work ({len(done)} conjectures already done)", file=sys.stderr)

    args.out.parent.mkdir(parents=True, exist_ok=True)
    run_start = time.monotonic()
    for i, oeis_id in enumerate(todo, 1):
        names = by_seq[oeis_id]
        content = build_input(oeis_id, names, records, histories)
        if args.show_input:
            print(f"\n{'#'*80}\nINPUT for {oeis_id} ({len(content)} chars):\n{content}")
        call_start = time.monotonic()
        try:
            result, usage = extract(client, content)
        except Exception as error:  # noqa: BLE001 -- log and move on; resumable rerun retries
            print(f"{time.strftime('%H:%M:%S')} [{i}/{len(todo)}] {oeis_id} FAILED after {time.monotonic()-call_start:.0f}s: {error}", file=sys.stderr)
            continue
        elapsed = time.monotonic() - call_start
        avg = (time.monotonic() - run_start) / i
        eta_min = avg * (len(todo) - i) / 60

        rows = {c["theorem_name"]: {"oeis_id": oeis_id, **c} for c in result["conjectures"]}
        # Guard against the model dropping/inventing a conjecture for this sequence.
        missing = [n for n in names if n not in rows]
        extra = [n for n in rows if n not in names]
        if missing or extra:
            print(f"{time.strftime('%H:%M:%S')} [{i}/{len(todo)}] {oeis_id} name mismatch missing={missing} extra={extra}", file=sys.stderr)
        with args.out.open("a", encoding="utf-8") as fh:
            for name in names:  # write only expected conjectures, in mapping order
                if name in rows:
                    fh.write(json.dumps(rows[name], ensure_ascii=False) + "\n")
        srcs = ",".join(sorted({c["match_source"] for c in result["conjectures"]}))
        print(f"{time.strftime('%H:%M:%S')} [{i}/{len(todo)}] {oeis_id} {len(names)} conj [{srcs}] "
              f"in {usage.prompt_tokens}/out {usage.completion_tokens} "
              f"| {elapsed:.0f}s (avg {avg:.0f}s, ETA {eta_min:.0f}m)", file=sys.stderr)


if __name__ == "__main__":
    main()
