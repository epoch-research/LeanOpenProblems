# type: ignore
"""FC100OpenSet1 frontend for the per-target isolation pipeline.

The dataset-neutral cut logic and Docker plumbing live in
``scripts/isolation.py``; this module owns what is FC100-specific:

* the data locations under ``apn/data/fc100open/`` and their parsers --
  membership comes from the vendored subset file ``FC100OpenSet1.lean`` (the
  paper's frozen 100-problem open set, arXiv 2605.13171) minus ``EXCLUDED.txt``
  (the 14 value-typed ``answer(sorry)`` members, unscorable by SafeVerify);
* the ``example``-command cut -- FC's hand-written problem files carry
  anonymous ``example`` sanity checks (GraphConjecture316/327) that run
  ``decide +native`` and would otherwise execute inside the trusted target
  compile on every score call, an infra fragility with zero spec value;
* the ``answer(sorry) ↔ P -> P`` rewrite -- FC states many open problems as
  ``answer(sorry) ↔ P``, where the propositional placeholder elaborates to
  ``True``, so the honest per-target spec is plain ``P``. The text surgery is
  certified by re-elaboration: the source target's raw-``Expr`` type must be
  exactly ``Iff True <rewritten type>`` (see :func:`iff_true` and
  ``tests/test_fc100_isolation.py``).

Two callers import this module: ``scripts/generate_fc100_isolated.py`` (the
vendor-time tool that produces ``Isolated/`` + ``MAPPING.txt``) and
``tests/test_fc100_isolation.py`` (the authoritative validation of the
committed files).
"""

from __future__ import annotations

import re

from apn.dataset import parse_fc100_mapping as parse_mapping  # re-exported
from scripts.isolation import REPO

FC100_DIR = REPO / "apn" / "data" / "fc100open"
SOURCES_DIR = FC100_DIR / "Sources"
ISOLATED_DIR = FC100_DIR / "Isolated"
SUBSET_FILE = FC100_DIR / "FC100OpenSet1.lean"
EXCLUDED_FILE = FC100_DIR / "EXCLUDED.txt"
MAPPING_FILE = FC100_DIR / "MAPPING.txt"

# Targets whose isolated spec may carry a `sorry` outside the target theorem.
# Wikipedia/EllipticCurveRank.lean declares its Mordell-Weil `Module.Finite`
# instance with `:= sorry` in FC itself; it is deliberately kept as-is (decided
# at task-addition time), so that sample implicitly also requires proving the
# instance. Generation reports it instead of failing.
SORRY_ALLOWLIST = {
    "EllipticCurveRank.RatEllipticCurve.twentyone_le_rank_height_count_asymptotic",
}

_DECL_NAME_RE = re.compile(r"decl_name%\s+([^\s,\]]+)")


def parse_subset_names(text: str) -> list[str]:
    """The member names listed in ``FC100OpenSet1.lean`` (its ``problems`` list
    of ``decl_name% <Name>`` entries), in file order."""
    return _DECL_NAME_RE.findall(text)


def parse_excluded(text: str) -> list[str]:
    """The excluded member names in ``EXCLUDED.txt`` (one per line; blank lines
    and ``#`` comments ignored)."""
    names: list[str] = []
    for line in text.splitlines():
        entry = line.split("#", 1)[0].strip()
        if entry:
            names.append(entry)
    return names


def kept_names() -> list[str]:
    """The 86 kept member names: the subset file's 100 minus ``EXCLUDED.txt``'s
    14, in subset-file order. Fails loudly if the membership arithmetic is off
    (a vendoring or exclusion-list error, never something to paper over)."""
    members = parse_subset_names(SUBSET_FILE.read_text())
    if len(members) != 100 or len(set(members)) != 100:
        raise SystemExit(f"expected 100 distinct subset members, found {len(members)}")
    excluded = parse_excluded(EXCLUDED_FILE.read_text())
    if len(excluded) != 14:
        raise SystemExit(f"expected 14 excluded members, found {len(excluded)}")
    unknown = sorted(set(excluded) - set(members))
    if unknown:
        raise SystemExit(f"EXCLUDED.txt names not in the subset: {unknown}")
    kept = [n for n in members if n not in set(excluded)]
    assert len(kept) == 86
    return kept


# An `example` command's span text: optional doc comment, then any `@[...]`
# attribute lists, then the `example` keyword. Matched against the span only
# for commands that introduced no declarations (Lean checks and discards an
# `example`, so it never appears in the environment diff) -- which is also why
# the generic theorem cut cannot see them and this text test is needed.
_EXAMPLE_RE = re.compile(rb"\A\s*(?:/--.*?-/\s*)?(?:@\[.*?\]\s*)*example\b", re.DOTALL)


def is_example_command(src: bytes, cmd: dict) -> bool:
    """Whether a no-decl command is an anonymous ``example``. These are FC's
    inline sanity tests; keeping them would make the *scorer* re-run their
    proofs (GraphConjecture316/327 use ``decide +native``) inside the trusted
    target compile on every score call, so the cut drops them like the named
    test lemmas."""
    if cmd["decls"]:
        return False
    return bool(_EXAMPLE_RE.match(src[cmd["declStart"] : cmd["declEnd"]]))


def fc100_kept_flags(src: bytes, filerec: dict, engine_flags: list[bool]) -> list[bool]:
    """FC's per-command keep decision: the engine's cut, plus cutting anonymous
    ``example`` commands."""
    return [
        keep and not is_example_command(src, c)
        for c, keep in zip(filerec["commands"], engine_flags)
    ]


# `answer(sorry) ↔ ` on the left of a statement (whitespace/newline tolerant).
# All 46 propositional uses in the subset are of this LHS form; an RHS form
# would leave `answer(` behind and fail generation's zero-`answer(` assertion.
_ANSWER_IFF_RE = re.compile(r"answer\(\s*sorry\s*\)\s*↔\s*")


def rewrite_answer_iff(text: str) -> tuple[str, int]:
    """Rewrite ``answer(sorry) ↔ P`` to plain ``P``; returns (text, #rewrites).

    The propositional ``answer(sorry)`` placeholder elaborates to a bare
    ``True`` (no mdata), so ``answer(sorry) ↔ P`` is definitionally just a
    dressed-up ``P`` -- but as stated it lets a submission prove ``True ↔ P``
    without the grader ever displaying an honest goal, and it would force
    ``answer(``-awareness into the agent prompt. The rewrite is certified
    exact by re-elaboration (:func:`iff_true`), never trusted as text surgery.
    """
    return _ANSWER_IFF_RE.subn("", text)


def strip_comments(text: str) -> str:
    """Lean text with all comments removed: nested ``/- ... -/`` blocks
    (including ``/--`` doc and ``/-!`` module comments) and ``--`` line
    comments. Used to census ``answer(`` in *code* -- kept documentation may
    legitimately mention ``answer(sorry)`` in prose (ErdosProblems/539.lean's
    module doc does), and prose is not the scoring surface."""
    out: list[str] = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j == -1 else j
        elif text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        else:
            if depth == 0:
                out.append(text[i])
            i += 1
    return "".join(out)


def iff_true(type_str: str) -> str:
    """The raw-``Expr`` string (the extractor's ``toString ci.type``) of
    ``True ↔ P``, given the raw-``Expr`` string of ``P``.

    Pinned against the container's actual output for `Erdos200.erdos_200`
    during implementation; ``toString`` on ``Expr`` is Lean's ``dbgToString``,
    which renders an application ``Iff True P`` in this fixed form. The
    certification gate asserts ``type(source target) == iff_true(type(isolated
    target))`` for every rewritten member (both sides hygiene-normalized, see
    :func:`normalize_hygiene`).
    """
    return f"Iff True ({type_str})"


# A macro-hygiene counter inside a binder name, e.g. `inst._@.17109…._hygCtx.
# _hyg.12` or `x._@.10237…._hygCtx.61.10237…._hygCtx._hyg.69`. Only the numbers
# directly following a `_hyg.`/`_hygCtx.` segment are matched, so mathematical
# content (numeric literals print as `OfNat.ofNat … 61 …`) can never be masked.
_HYG_NUM_RE = re.compile(r"(_hyg(?:Ctx)?\.)\d+")


def normalize_hygiene(type_str: str) -> str:
    """Erase macro-hygiene counter values from binder names in a raw-``Expr``
    string.

    Anonymous binders (instance-implicits, ``match`` discriminants) get names
    embedding the command's macro-scope counter. The counter advances with each
    macro expansion *within* a command (it restarts per command, which is why
    plain sibling-cutting never shifts it), so removing ``answer(sorry) ↔``
    from a statement shifts the indices of every hygienic binder downstream of
    it -- 5 of the 46 rewritten members have such binders. Binder names are
    display-only (the printed term is otherwise de Bruijn-faithful), so
    equality up to these counter values is α-equivalence, exactly the
    certificate we want."""
    return _HYG_NUM_RE.sub(r"\g<1>N", type_str)
