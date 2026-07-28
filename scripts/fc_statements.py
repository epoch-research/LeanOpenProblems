"""Formal-Conjectures statement conventions, shared by the FC-derived datasets.

The FC repository states problems with conventions that are not specific to any
one subset of it: anonymous ``example`` sanity checks alongside the target
theorems, and the ``answer( )`` elaborator for "is it true that P?" problems.
This module owns the helpers that deal with those conventions -- the
``example``-command cut, the ``answer(...) ↔`` rewrite and its re-elaboration
certificates, and the comment/hygiene normalizers they rely on. The
dataset-specific frontends (``scripts/fc100_isolation.py``,
``scripts/erdos_isolation.py``) own only data locations and membership parsing;
the dataset-neutral cut engine lives in ``scripts/isolation.py``.

The ``answer( )`` convention. FC states "is it true that P?" problems as
``theorem foo : answer(sorry) ↔ P := by sorry``; a solver is meant to replace
the inner ``sorry`` with ``True`` or ``False`` and prove the resulting iff.
In the elaborator's default mode a *propositional* ``answer(sorry)`` elaborates
to a bare ``True``, so the unfilled statement is definitionally just ``P`` --
but as stated it lets a submission prove ``True ↔ P`` without the grader ever
displaying an honest goal, and it would force ``answer(``-awareness into the
agent prompt. Once a problem is resolved, FC records the verdict by filling the
literal -- ``answer(True) ↔ P`` or ``answer(False) ↔ P`` -- while the proof
stays ``sorry``; a filled literal is the answer key and must not leak into a
shipped spec. Our treatment strips the answer half of the iff and ships plain
``P``: the agent proves ``P`` or disproves it via ``foo.disproof`` (``¬P``),
exactly the original task. The text surgery is certified by re-elaboration
(:func:`answer_certificate`), never trusted as a regex.
"""

from __future__ import annotations

import re


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


def fc_kept_flags(src: bytes, filerec: dict, engine_flags: list[bool]) -> list[bool]:
    """FC's per-command keep decision: the engine's cut, plus cutting anonymous
    ``example`` commands."""
    return [
        keep and not is_example_command(src, c)
        for c, keep in zip(filerec["commands"], engine_flags)
    ]


# FC tags every problem statement with a `@[category ..., AMS ...]`
# classification list. It is catalogue metadata, not part of the mathematical
# statement -- and its category field (`research open`/`solved`) plus any
# `formal_proof` URL clause are where FC records resolution status, an
# answer-key channel for the eval tasks -- so the shipped specs drop the list
# whole (with its trailing newline). Only lists *starting* with `category` are
# matched: semantic attributes (Selfridge's `@[mk_iff]`) live in their own
# lists and must be kept. Anchored to line starts, where every real attribute
# list sits -- prose may quote the attribute mid-line (OpenQuantumProblems/23's
# module doc does) and must not be mangled.
CATEGORY_ATTR_RE = re.compile(r"^@\[category [^\]]*\]\n?", re.MULTILINE)


def strip_category_attrs(text: str) -> tuple[str, int]:
    """Remove every ``@[category ...]`` classification list from an isolated
    spec's text; returns (text, #removed). Elaboration-neutral -- attributes
    never reach the statement's type -- and the certificate + compile gates
    re-check the result; the generation scripts assert the per-dataset count."""
    return CATEGORY_ATTR_RE.subn("", text)


# The `answer(...) ↔` convention's surface forms. LHS carries the placeholder
# or a recorded verdict literal; the RHS form only ever appears unfilled
# (a filled RHS would extend the pattern and fail generation's
# zero-`answer(` assertion, loudly). The LHS pattern consumes only *horizontal*
# trailing whitespace: when the iff's right side starts on its own line
# (ErdosProblems/1139.lean continues with an indentation-sensitive `letI`
# block), eating the newline would splice that block onto the header line and
# silently change the parse.
_ANSWER_LHS_RE = re.compile(r"answer\(\s*(sorry|True|False)\s*\)\s*↔[ \t]*")
_ANSWER_RHS_RE = re.compile(r"\s*↔\s*answer\(\s*sorry\s*\)")

# Form labels, as returned by :func:`detect_answer_form` and
# :func:`rewrite_answer_iff` and consumed by :func:`answer_certificate`.
LHS_SORRY = "lhs_sorry"  # answer(sorry) ↔ P
LHS_TRUE = "lhs_true"  # answer(True) ↔ P   (recorded verdict: P holds)
LHS_FALSE = "lhs_false"  # answer(False) ↔ P  (recorded verdict: ¬P holds)
RHS_SORRY = "rhs_sorry"  # P ↔ answer(sorry)


def detect_answer_form(code: str) -> str | None:
    """The ``answer(...) ↔`` form of a statement's comment-stripped source
    text, or ``None`` for a plain proposition. Raises on anything else (several
    ``answer(`` occurrences, or a form outside the four known ones -- e.g. a
    value-typed placeholder), so an unnoticed new upstream convention can never
    be classified silently."""
    n = code.count("answer(")
    if n == 0:
        return None
    if n > 1:
        raise ValueError(f"{n} answer( occurrences in one statement")
    m = _ANSWER_LHS_RE.search(code)
    if m:
        return f"lhs_{m.group(1).lower()}"
    if _ANSWER_RHS_RE.search(code):
        return RHS_SORRY
    raise ValueError(f"unrecognized answer( form: {' '.join(code.split())[:200]}")


def rewrite_answer_iff(text: str) -> tuple[str, str | None, int]:
    """Rewrite the ``answer(...) ↔`` half out of ``text``, leaving plain ``P``:
    LHS ``answer(sorry|True|False) ↔ P`` and RHS ``P ↔ answer(sorry)`` are both
    handled. Returns ``(text, form, n_rewrites)``; callers assert exactly one
    rewrite happened and re-census ``answer(`` afterwards. A filled literal is
    un-filled by this on purpose -- determining P's truth value is the task,
    and the recorded verdict is the answer key. The rewrite is certified exact
    by re-elaboration (:func:`answer_certificate`)."""
    m = _ANSWER_LHS_RE.search(text)
    if m:
        out, n = _ANSWER_LHS_RE.subn("", text)
        return out, f"lhs_{m.group(1).lower()}", n
    if _ANSWER_RHS_RE.search(text):
        out, n = _ANSWER_RHS_RE.subn("", text)
        return out, RHS_SORRY, n
    return text, None, 0


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


# Per-form certificate wrapper text, pinned against the container's actual
# extractor output for one probe theorem per form. The unfilled propositional
# ``answer(sorry)`` elaborates to a bare ``True``; a *filled* literal takes the
# elaborator's annotation path instead and so carries an ``[mdata answer:1 ...]``
# wrapper in ``dbgToString``. Each form lists its (head, tail) insertion pair
# in both argument renderings: ``dbgToString`` parenthesizes a compound
# application argument but prints an atomic one (a bare constant) without
# parens (Erdos945's conclusion is the const ``Erdos945Prop``).
_WRAPPERS = {
    LHS_SORRY: (("Iff True (", ")"), ("Iff True ", "")),
    LHS_TRUE: (("Iff ([mdata answer:1 True]) (", ")"), ("Iff ([mdata answer:1 True]) ", "")),
    LHS_FALSE: (("Iff ([mdata answer:1 False]) (", ")"), ("Iff ([mdata answer:1 False]) ", "")),
    RHS_SORRY: (("Iff (", ") True"), ("Iff ", " True")),
}


def _is_insertion(src: str, iso: str, head: str, tail: str) -> bool:
    """Whether ``src == iso[:a] + head + iso[a:b] + tail + iso[b:]`` for some
    ``a <= b`` -- i.e. ``src`` is exactly ``iso`` with the wrapper's two texts
    inserted. Every candidate pair is tried; the full-equality requirement
    pins everything outside the inserted texts, so an ambiguous match can only
    be a second valid decomposition of the same relation."""
    if len(src) != len(iso) + len(head) + len(tail):
        return False
    a = 0
    while (a := src.find(head, a)) != -1:
        if src[:a] == iso[:a]:
            rest = src[:a] + src[a + len(head) :]  # src with head deleted
            if not tail:
                if rest == iso:
                    return True
            else:
                b = a
                while (b := rest.find(tail, b)) != -1:
                    if rest[:b] == iso[:b] and rest[b + len(tail) :] == iso[b:]:
                        return True
                    b += 1
        a += 1
    return False


def answer_certified(form: str | None, src_type: str, iso_type: str) -> bool:
    """Whether the *source* statement's raw-``Expr`` string is exactly the
    isolated statement's with the detected form's ``Iff``-wrapper inserted
    around the conclusion. This is the re-elaboration certificate of
    :func:`rewrite_answer_iff`: Lean's own elaborator, not the regex, vouches
    that the shipped ``P`` means exactly what the source statement meant.

    The wrapper is *inserted*, not applied around the whole type: binders
    before the colon hoist over the iff (``theorem foo (x) : answer(sorry) ↔ P``
    elaborates to ``forall x, Iff True P``), so the ``Iff`` head sits under the
    binder telescope -- and when the hoisting binders are printed
    parenthesized (an arrow codomain, Erdos282's ``variants.graham``), the
    wrapper's closing text lands *inside* the enclosing parens rather than at
    the end of the string, hence the two independent insertion points of
    :func:`_is_insertion`. Compare both sides through :func:`normalize_hygiene`
    first.
    """
    if form is None:
        return src_type == iso_type
    return any(
        _is_insertion(src_type, iso_type, head, tail) for head, tail in _WRAPPERS[form]
    )


# A hygienic binder name's macro-scope tail, e.g. `x._@.10237…._hygCtx.61.
# 10237…._hygCtx._hyg.69` -- `._@.` marks a macro-scoped name (it cannot occur
# in an ordinary identifier) and everything after it is scope bookkeeping:
# context hashes, scope indices, `_hygCtx`/`_hyg` markers, in nesting-dependent
# alternation (the context hash repeats per scope level, so anchoring on the
# markers alone misses hashes that follow an index segment -- Erdos897). The
# whole tail is masked, up to the nearest expression delimiter; the meaningful
# display part of the name (`x`, `inst`) precedes `._@.` and is kept.
# Mathematical content (numeric literals print as `OfNat.ofNat … 61 …`) can
# never be masked. `_HYG_NUM_RE` still covers hygiene counters in names
# without the `._@.` prefix.
_HYG_TAIL_RE = re.compile(r"\._@\.[^\s()\[\]{},:]*")
_HYG_NUM_RE = re.compile(r"(_hyg(?:Ctx)?\.)\d+")

# A pattern-match auxiliary declaration's qualified name, e.g.
# `Erdos324.erdos_324.match_1.{1}` (the qualifier is the declaration Lean
# elaborated the match *for*). Name characters can never include the
# delimiters dbgToString puts around applications, so the match is exact.
_MATCH_AUX_RE = re.compile(r"[^\s()\[\]{},]*\.match_\d+")


def normalize_hygiene(type_str: str) -> str:
    """Erase elaboration-context-dependent display artifacts from a
    raw-``Expr`` string: the macro-scope tails of hygienic binder names, and
    the owner-qualified names of pattern-match auxiliaries.

    Anonymous binders (instance-implicits, ``match`` discriminants) get names
    embedding the command's macro-scope chain -- context hashes and counters.
    The counter advances with each macro expansion *within* a command (it
    restarts per command, which is why plain sibling-cutting never shifts it),
    so removing ``answer(sorry) ↔`` from a statement shifts the indices of
    every hygienic binder downstream of it -- 5 of the 46 rewritten FC100
    members have such binders -- and the context hash can differ outright
    between the source and isolated elaborations of one statement (Erdos897).

    A pattern-matching lambda elaborates to an auxiliary ``<owner>.match_<n>``
    declaration, and Lean *reuses* an earlier declaration's auxiliary when the
    patterns coincide -- so a statement's printed type can name a cut sibling's
    auxiliary in the source yet its own in the isolated file
    (ErdosProblems/324.lean's ``erdos_324.variants.quintic`` names
    ``erdos_324.match_1``). The auxiliaries are definitionally identical by
    construction of the reuse, and the motive and discriminants stay in the
    compared text.

    All these artifact kinds are display-only (the printed term is otherwise
    de Bruijn-faithful), so equality up to them is α-equivalence, exactly the
    certificate we want."""
    type_str = _HYG_TAIL_RE.sub("._@.H", type_str)
    type_str = _HYG_NUM_RE.sub(r"\g<1>N", type_str)
    return _MATCH_AUX_RE.sub("match_N", type_str)
