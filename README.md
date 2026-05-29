# AlphaProof Nexus on Inspect

An open reimplementation of the agent framework from Tsoukalas et al.,
*Advancing Mathematics Research with AI-Driven Formal Proof Search*
(arXiv:2605.22763v1), built as an [Inspect](https://inspect.aisi.org.uk)
evaluation.

The paper describes **AlphaProof Nexus**, a framework for LLM-driven Lean proof
search, with four agent tiers on a shared generation/validation pipeline:

| Tier | Description | Status here |
|------|-------------|-------------|
| **A** basic | Independent "Ralph-loop" prover subagents that refine a Lean proof sketch with Inspect's `text_editor` tool, guided by Lean compiler feedback. | **Implemented** |
| **B** | A + an AlphaProof proof tool. | Pluggable tool interface planned; AlphaProof itself is proprietary. |
| **C** | A + an evolutionary population database (Plackett–Luce Elo via Gibbs sampling, Thompson sampling, P-UCB selection, LLM rater agents). | Planned |
| **D** full | A + AlphaProof + evolution. | Planned |

This repository currently implements **tier A** end to end, against a **real
Lean 4 + Mathlib + Pantograph** sandbox.

## Architecture

```
apn/
  sketch.py            ProofSketch: EVOLVE-BLOCK/EVOLVE-VALUE parsing, sorry
                       detection, frozen-skeleton extraction (for integrity).
  safeverify.py        SafeVerify: compiles + statement-integrity + axiom guard.
  verifier/
    base.py            LeanVerifier protocol, CompileResult, AxiomResult.
    pantograph.py      Host-side verifier that drives the sandbox daemon.
    fake.py            In-process fake verifier for offline tests.
  tools.py             lean_check tool (compile the file; editing is done with
                       Inspect's built-in text_editor tool).
  prompts.py           Basic-agent prompt (Figure 5, adapted for text_editor).
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
2. `N` prover subagents run independently, **each in its own Lean sandbox**. Each
   is a **Ralph loop** of **episodes**. An episode is a multi-turn LLM session in
   which the model edits the file with Inspect's `text_editor` tool and compiles
   it with `lean_check`, iterating on the compiler feedback.
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

Each subagent gets **its own sandbox** (`apn_basic` provisions one Docker
service per subagent), so `text_editor` edits and compilation are isolated.
`num_subagents` containers run per problem, so keep it small locally.

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
  --model anthropic/claude-sonnet-4-5 \
  -T num_subagents=2 -T max_episodes=10
```

Point at your own sketches with `-T sketches_dir=/path/to/lean/sketches`
(each `*.lean` file is one problem). Any Inspect-supported model works; the
paper used Gemini 3.1 Pro for proving.

The first compile in each sample's sandbox imports Mathlib (~1–2 minutes); after
that the warm Pantograph server makes compiles fast.

### API keys

Provider keys live in `.env`. Inspect loads `.env` but does not override a
variable already set in the environment, so if your shell exports an empty
`ANTHROPIC_API_KEY` (etc.) it will shadow the `.env` value. Export the key
explicitly for the run if needed:

```bash
export ANTHROPIC_API_KEY="$(python -c "from dotenv import dotenv_values; print(dotenv_values('.env')['ANTHROPIC_API_KEY'])")"
```

## Development

```bash
uv sync
uv run mypy                    # strict type checking (Inspect ships precise types)
uv run pytest -m "not slow"    # fast unit tests (no Docker or network)
uv run pytest -m slow          # Docker-gated agent integration tests
```

The fast tests cover the pure logic (sketch model, SafeVerify, the daemon's
parsers, dataset, prompt) with no Docker or network. The agent's full
orchestration is exercised by the Docker-gated `slow` tests, which drive the
real `text_editor` tool and per-subagent sandboxes with a scripted `mockllm`
model and the in-process `FakeVerifier` (so they need the `apn-lean` image but
no real model or Lean compilation).

## Not yet implemented

- AlphaProof tool (tier B) — proprietary; will be a pluggable interface.
- Evolutionary population database, Elo rating, P-UCB, rater agents (tiers C/D).
- Global goal caching.
- A Formal Conjectures Erdős loader (the bundled dataset is a small smoke set).
