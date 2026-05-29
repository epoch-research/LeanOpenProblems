# AlphaProof Nexus on Inspect

An open reimplementation of the agent framework from Tsoukalas et al.,
*Advancing Mathematics Research with AI-Driven Formal Proof Search*
(arXiv:2605.22763v1), built as an [Inspect](https://inspect.aisi.org.uk)
evaluation.

The paper describes **AlphaProof Nexus**, a framework for LLM-driven Lean proof
search, with four agent tiers on a shared generation/validation pipeline:

| Tier | Description | Status here |
|------|-------------|-------------|
| **A** basic | A prover that refines a Lean proof sketch guided by compiler feedback. Implemented as Inspect's built-in `deepagent` with `text_editor` + `lean_check`; run independent attempts with `--epochs`. | **Implemented** |
| **B** | A + an AlphaProof proof tool. | Pluggable tool interface planned; AlphaProof itself is proprietary. |
| **C** | A + an evolutionary population database (Plackett–Luce Elo via Gibbs sampling, Thompson sampling, P-UCB selection, LLM rater agents). | Planned |
| **D** full | A + AlphaProof + evolution. | Planned |

This repository currently implements **tier A** end to end, against a **real
Lean 4 + Mathlib + Pantograph** sandbox.

## Architecture

The agent is deliberately thin: it is Inspect's built-in
[`deepagent`](https://inspect.aisi.org.uk) given the proof file plus two tools.
The bespoke parts of the paper (EVOLVE-marker editing, a `ProofSketch` model, an
explicit episode/Ralph loop, and hand-rolled parallel subagents) are gone; what
remains is Lean integration and a strict scorer.

```
apn/
  agent.py             lean_prover solver: writes the proof file into the
                       sandbox, runs a deepagent (text_editor + lean_check),
                       reads the result back.
  tools.py             lean_check tool (compile the file via the sandbox).
  prompts.py           Instructions + task message for the agent.
  safeverify.py        Validation: compiles + statement preserved (verbatim) +
                       axiom guard. The anti-cheat.
  verifier/
    base.py            LeanVerifier protocol, CompileResult, AxiomResult.
    pantograph.py      Host-side verifier that drives the sandbox daemon.
    fake.py            In-process fake verifier for offline tests.
  scorer.py            Re-validates the final proof; correct iff complete proof.
  dataset.py           Lean sketches (theorem + sorry) -> Inspect Samples.
  task.py              The apn_basic Inspect task.
  lean/                Docker image + sandbox-side Pantograph daemon.
```

### How a proof search runs

1. The input is a Lean file containing a theorem whose proof is `sorry`.
2. `lean_prover` writes it into the sample's sandbox and runs a `deepagent`. The
   agent edits the file with the built-in `text_editor` tool and compiles it with
   `lean_check`, iterating on the Lean compiler feedback until it submits.
3. The scorer independently re-validates the final file with **SafeVerify**: it
   must compile, keep the theorem statement **verbatim** (so the goal can't be
   weakened to `True`), be `sorry`-free, and use only permitted axioms.
4. Run several independent attempts per problem by passing `--epochs N` at eval
   time; each epoch is a fresh sample run with its own sandbox.

## Lean sandbox

Lean runs in Docker (`apn/lean/`), matching the paper's isolated sandboxes. Each
sample gets **two** sandboxes from a shared Mathlib base image:

* **`default`** — the agent's workspace (`apn-agent`): a warm
  [PyPantograph](https://github.com/lenianiva/PyPantograph) server holds a single
  `pantograph-repl` process with Mathlib loaded behind a Unix socket, so the many
  `lean_check` compiles an attempt makes don't each re-import Mathlib. **No
  SafeVerify here.**
* **`scorer`** — a separate, trusted container (`apn-scorer`) the agent never
  writes to, where SafeVerify validates the final proof. The scorer writes the
  submitted proof (from the store) into this clean container and checks it, so
  the agent cannot tamper with the checker, the target spec, or the oleans.

Each sample (and each epoch) gets its own pair of sandboxes.

**Version note.** The image pins **Lean v4.29.1** and **Mathlib v4.29.1**,
matching the Lean toolchain that the pinned PyPantograph commit builds its repl
against (the three must agree for the repl to load Mathlib's `.olean` files).
The paper used Lean v4.27; v4.29.1 is the nearest toolchain PyPantograph
provides.

SafeVerify is vendored under `apn/lean/safeverify/` (ported to Lean v4.29.1; see
its `NOTICE.md`).

### Build the images

```bash
apn/lean/build.sh   # builds apn-lean-base, then apn-agent and apn-scorer
```

This fetches Mathlib's prebuilt `.olean` cache (`lake exe cache get`) into a base
image, then layers PyPantograph (agent) and SafeVerify (scorer) on top. The
images are large (Mathlib dominates).

## Running

```bash
# Build the Lean images first (above), then:
inspect eval apn/task.py@apn_basic \
  --model anthropic/claude-sonnet-4-5 \
  --epochs 4
```

`--epochs N` runs N independent attempts per problem, each in its own sandbox.
Point at your own sketches with `-T sketches_dir=/path/to/lean/sketches` (each
`*.lean` file is one theorem with a `sorry` proof). Any Inspect-supported model
works; the paper used Gemini 3.1 Pro for proving.

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
uv run mypy        # strict type checking (Inspect ships precise types)
uv run pytest      # unit tests (no Docker or network)
```

The unit tests cover the pure logic (SafeVerify, the daemon's parsers, dataset,
prompts) with no Docker or network. The agent itself is `deepagent`, so it is
validated by running a real eval against the Lean sandbox (above).

## Not yet implemented

- AlphaProof tool (tier B) — proprietary; will be a pluggable interface.
- Evolutionary population database, Elo rating, P-UCB, rater agents (tiers C/D).
- Global goal caching.
- A Formal Conjectures Erdős loader (the bundled dataset is a small smoke set).
