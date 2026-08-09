"""Classify conjecture proposers (academic / amateur / ...) from OEIS wiki user pages.

Every registered OEIS contributor has a self-written wiki user page
(https://oeis.org/wiki/User:<Name>) that usually states occupation or
affiliation. We fetch the raw wikitext for each unique proposer named in
conjecture_provenance.jsonl and have an LLM produce a structured profile.

Pages are cached in apn/data/oeis/raw/proposer_pages.jsonl; output rows are
appended to apn/data/oeis/proposer_metadata.jsonl and runs are resumable.

Model: gpt-5.5, medium reasoning effort, strict structured output.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import threading
import urllib.error
import urllib.parse
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import openai

from extract_provenance import load_env

ROOT = Path(__file__).parent.parent
PROVENANCE = ROOT / "apn" / "data" / "oeis" / "conjecture_provenance.jsonl"
PAGES = ROOT / "apn" / "data" / "oeis" / "raw" / "proposer_pages.jsonl"

MODEL = "gpt-5.5"
USER_AGENT = "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7)"
REDIRECT_RE = re.compile(r"#REDIRECT\s*\[\[(.*?)\]\]", re.IGNORECASE)


def unique_proposers() -> list[str]:
    names: dict[str, None] = {}
    for line in PROVENANCE.read_text().splitlines():
        if not line.strip():
            continue
        proposer = json.loads(line).get("proposer")
        if not proposer:
            continue
        # Joint attributions use " and "; commas are name suffixes ("..., Jr.").
        for name in proposer.split(" and "):
            if name.strip():
                names.setdefault(name.strip())
    return list(names)


def fetch_page(name: str) -> dict:
    """Raw wikitext of the User: page, following one #REDIRECT hop."""
    title = name.replace(" ", "_")
    for _ in range(2):
        url = f"https://oeis.org/wiki/User:{urllib.parse.quote(title)}?action=raw"
        req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        try:
            wikitext = urllib.request.urlopen(req, timeout=30).read().decode("utf-8", "replace")
        except urllib.error.HTTPError as error:
            if error.code == 404:
                return {"name": name, "title": title, "status": "missing", "wikitext": None}
            raise
        redirect = REDIRECT_RE.match(wikitext.strip())
        if not redirect:
            return {"name": name, "title": title, "status": "ok", "wikitext": wikitext}
        title = redirect.group(1).removeprefix("User:")
    return {"name": name, "title": title, "status": "redirect_loop", "wikitext": None}


def load_pages() -> dict[str, dict]:
    if not PAGES.is_file():
        return {}
    return {
        json.loads(line)["name"]: json.loads(line)
        for line in PAGES.read_text().splitlines()
        if line.strip()
    }


SYSTEM = """\
You classify contributors to the OEIS (Online Encyclopedia of Integer Sequences), \
given their self-written OEIS wiki user page. The goal is to distinguish professional \
mathematicians and other academics from amateurs/hobbyists.

Use BOTH the wiki page and your background knowledge. Many OEIS contributors are \
well-known mathematicians or long-time figures in the community whose occupation you \
know even when their wiki page is terse -- use what you know and set evidence_source \
accordingly. Only fall back to "unknown" when the page is uninformative AND you have \
no reliable knowledge of the person; never infer a category from the name alone.

Categories:
- academic_mathematician: holds or held an academic/research position in mathematics \
(professor, postdoc, research mathematician).
- academic_other: academic/research position in another field (physics, CS, biology, ...).
- industry_professional: works in industry (engineer, software developer, actuary, ...), \
mathematics is not their profession.
- student: currently a student (any level) and not otherwise employed as above.
- amateur: hobbyist / independent enthusiast; no academic or quantitative-professional role \
stated or known.
- unknown: page missing or uninformative, and no reliable background knowledge.

Notes: classify by occupation, current or past ("retired X" counts as X). If the evidence \
is partial -- a PhD with no stated position, listed research publications, OEIS editorship -- \
record it in occupation (e.g. "PhD in mathematics; position unknown") even when the category \
must stay unknown. Put a short verbatim quote (or the background fact) in evidence.\
"""

SCHEMA = {
    "type": "object",
    "additionalProperties": False,
    "properties": {
        "category": {
            "type": "string",
            "enum": [
                "academic_mathematician",
                "academic_other",
                "industry_professional",
                "student",
                "amateur",
                "unknown",
            ],
        },
        "occupation": {"type": ["string", "null"]},
        "affiliation": {"type": ["string", "null"]},
        "evidence_source": {"type": "string", "enum": ["wiki_page", "background_knowledge", "both", "none"]},
        "evidence": {"type": "string"},
        "confidence": {"type": "string", "enum": ["high", "medium", "low"]},
    },
    "required": ["category", "occupation", "affiliation", "evidence_source", "evidence", "confidence"],
}


def classify(client: openai.OpenAI, name: str, page: dict) -> dict:
    body = page["wikitext"] if page["status"] == "ok" else f"(no wiki user page found: {page['status']})"
    resp = client.chat.completions.create(
        model=MODEL,
        reasoning_effort="medium",
        response_format={"type": "json_schema", "json_schema": {"name": "proposer", "schema": SCHEMA, "strict": True}},
        messages=[
            {"role": "system", "content": SYSTEM},
            {"role": "user", "content": f"Contributor: {name}\n\nOEIS wiki user page (raw wikitext):\n{body}"},
        ],
    )
    return json.loads(resp.choices[0].message.content)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", type=Path, default=ROOT / "apn" / "data" / "oeis" / "proposer_metadata.jsonl")
    ap.add_argument("--all", action="store_true", help="process every proposer")
    ap.add_argument("--n", type=int, default=10, help="first N proposers (ignored with --all)")
    ap.add_argument("--workers", type=int, default=16)
    args = ap.parse_args()

    load_env()
    client = openai.OpenAI(timeout=120.0, max_retries=2)
    proposers = unique_proposers()
    targets = proposers if args.all else proposers[: args.n]

    pages = load_pages()
    PAGES.parent.mkdir(parents=True, exist_ok=True)
    lock = threading.Lock()

    def fetch_one(name: str) -> None:
        page = fetch_page(name)
        with lock:
            pages[name] = page
            with PAGES.open("a", encoding="utf-8") as fh:
                fh.write(json.dumps(page, ensure_ascii=False) + "\n")
        print(f"fetched {name}: {page['status']}", file=sys.stderr)

    to_fetch = [n for n in targets if n not in pages]
    with ThreadPoolExecutor(max_workers=8) as pool:
        list(pool.map(fetch_one, to_fetch))

    done = set()
    if args.out.is_file():
        done = {json.loads(l)["name"] for l in args.out.read_text().splitlines() if l.strip()}
    todo = [n for n in targets if n not in done]
    print(f"{len(targets)} proposers targeted; {len(todo)} need classification", file=sys.stderr)

    def classify_one(name: str) -> None:
        try:
            row = {"name": name, "page_status": pages[name]["status"], **classify(client, name, pages[name])}
        except Exception as error:  # noqa: BLE001 -- log and move on; resumable rerun retries
            print(f"{name} FAILED: {error}", file=sys.stderr)
            return
        with lock:
            with args.out.open("a", encoding="utf-8") as fh:
                fh.write(json.dumps(row, ensure_ascii=False) + "\n")
        print(f"{name}: {row['category']} ({row['confidence']})", file=sys.stderr)

    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        list(pool.map(classify_one, todo))


if __name__ == "__main__":
    main()
