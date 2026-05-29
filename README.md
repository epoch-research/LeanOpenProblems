# AlphaProof Nexus on Inspect

An open reimplementation of the agent framework from Tsoukalas et al.,
*Advancing Mathematics Research with AI-Driven Formal Proof Search*
(arXiv:2605.22763v1), built as an [Inspect](https://inspect.aisi.org.uk)
evaluation.

The paper describes **AlphaProof Nexus**, a framework for LLM-driven Lean proof
search, with four agent tiers on a shared generation/validation pipeline:

| Tier | Description | Status here |
|------|-------------|-------------|
| **A** basic | Independent "Ralph-loop" prover subagents that refine a Lean proof sketch via a `search_replace` tool, guided by Lean compiler feedback. | **Implemented** |
| **B** | A + an AlphaProof proof tool. | Pluggable tool interface planned; AlphaProof itself is proprietary. |
| **C** | A + an evolutionary population database (Plackett–Luce Elo via Gibbs sampling, Thompson sampling, P-UCB selection, LLM rater agents). | Planned |
| **D** full | A + AlphaProof + evolution. | Planned |

This repository currently implements **tier A** end to end, against a **real
Lean 4 + Mathlib + Pantograph** sandbox.

## Architecture

```
apn/
  sketch.py            ProofSketch: EVOLVE-BLOCK/EVOLVE-VALUE parsing, sorry
                       detection, frozen-skeleton extraction, search/replace.
  safeverify.py        SafeVerify: compiles + statement-integrity + axiom guard.
  verifier/
    base.py            LeanVerifier protocol, CompileResult, AxiomResult.
    pantograph.py      Host-side verifier that drives the sandbox daemon.
    fake.py            In-process fake verifier for offline tests.
  tools.py             search_replace tool (compact-diff edits + recompile).
  prompts.py           Basic-agent prompt (Figure 5, verbatim).
  agents/basic.py      Basic agent: episode loop, Ralph loop, N subagents.
  scorer.py            Re-validates the final sketch; correct iff complete proof.
  dataset.py           Lean sketches -> Inspect Samples.
  task.py              The apn_basic Inspect task.
  lean/                Docker image + sandbox-side Pantograph daemon.
```

### How a proof search runs (tier A)

1. The input is a *proof sketch*: a Lean file with the proof replaced by `sorry`
   inside `-- EVOLVE-BLOCK-START`/`-- EVOLVE-BLOCK-END` markers. Only text inside
   EVOLVE regions may change, so the target theorem statement is frozen.
2. `N` prover subagents run independently. Each is a **Ralph loop** of
   **episodes**. An episode is a multi-turn LLM session with the `search_replace`
   tool; after every edit the Lean compiler runs and its messages feed the next
   turn.
3. When an episode's session ends, **SafeVerify** validates the sketch: it must
   compile, leave the statement intact, and use no disallowed axioms (`sorryAx`
   is tolerated only while a `sorry` legitimately remains). A validated,
   `sorry`-free sketch is a complete proof.
4. The first subagent to find a complete proof wins; the rest are cancelled.

## Lean sandbox

Lean compilation runs in Docker (`apn/lean/`), matching the paper's isolated
sandboxes. A warm [PyPantograph](https://github.com/lenianiva/PyPantograph)
server holds a single `pantograph-repl` process with Mathlib loaded, behind a
Unix socket, so the many compile calls an episode makes don't each re-import
Mathlib.

**Version note.** The image pins **Lean v4.29.1** and **Mathlib v4.29.1**,
matching the Lean toolchain that the pinned PyPantograph commit builds its repl
against (the three must agree for the repl to load Mathlib's `.olean` files).
The paper used Lean v4.27; v4.29.1 is the nearest toolchain PyPantograph
provides.

### Build the image

```bash
docker build -t apn-lean apn/lean
```

This fetches Mathlib's prebuilt `.olean` cache (`lake exe cache get`) and builds
the Pantograph repl; the resulting image is large (~11 GB).

## Running

```bash
# Build the Lean image first (above), then:
inspect eval apn/task.py@apn_basic \
  --model anthropic/claude-sonnet-4-6 \
  -T num_subagents=4 -T max_episodes=10
```

Point at your own sketches with `-T sketches_dir=/path/to/lean/sketches`
(each `*.lean` file is one problem). Any Inspect-supported model works; the
paper used Gemini 3.1 Pro for proving.

## Development

```bash
uv sync
uv run mypy        # strict type checking (Inspect ships precise types)
uv run pytest      # unit tests (no Docker or network required)
```

The agent loop is tested deterministically with Inspect's `mockllm` provider and
the in-process `FakeVerifier`, so the full pipeline runs without a model or the
Lean toolchain.

## Not yet implemented

- AlphaProof tool (tier B) — proprietary; will be a pluggable interface.
- Evolutionary population database, Elo rating, P-UCB, rater agents (tiers C/D).
- Global goal caching.
- A Formal Conjectures Erdős loader (the bundled dataset is a small smoke set).
