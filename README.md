# AlphaProof Nexus on Inspect

An open reimplementation of the agent framework from Tsoukalas et al.,
*Advancing Mathematics Research with AI-Driven Formal Proof Search*
(arXiv:2605.22763v1), built as an [Inspect](https://inspect.aisi.org.uk)
evaluation.

The paper describes **AlphaProof Nexus**, a framework for LLM-driven Lean proof
search, with four agent tiers on a shared generation/validation pipeline:

| Tier | Description | Status here |
|------|-------------|-------------|
| **A** basic | A prover that refines a Lean proof sketch guided by compiler feedback. Implemented as Inspect's built-in `deepagent` with `text_editor` + `bash` (drives [PyPantograph](https://github.com/lenianiva/PyPantograph) from python3 for Lean compilation and goal interaction; sympy/numpy for numeric exploration); run independent attempts with `--epochs`. | **Implemented** |
| **B** | A + an AlphaProof proof tool. | Pluggable tool interface planned; AlphaProof itself is proprietary. |
| **C** | A + an evolutionary population database (Plackett–Luce Elo via Gibbs sampling, Thompson sampling, P-UCB selection, LLM rater agents). | Planned |
| **D** full | A + AlphaProof + evolution. | Planned |

This repository implements **tier A** end to end, against a **real Lean 4 +
Mathlib + Pantograph** sandbox, and runs it on the paper's **OEIS** benchmark:
the 492 autoformalized OEIS conjectures (`apn_oeis`), of which the paper solved
44. (`gpt-5.5` has solved real conjectures from the set through this pipeline.)

The Erdős set (`erdos_problems_attempted.txt`, 352 problems) is the next target;
most of those use the `answer(...)` macro, which needs the answer-aware scorer
described under *Not yet implemented*.

## Architecture

The agent is deliberately thin: it is Inspect's built-in
[`deepagent`](https://inspect.aisi.org.uk) given the proof file plus a few tools.
The bespoke parts of the paper (EVOLVE-marker editing, a `ProofSketch` model, an
explicit episode/Ralph loop, and hand-rolled parallel subagents) are gone; what
remains is Lean integration and a strict scorer.

```
apn/
  agent.py             lean_prover solver: writes the proof file into the
                       sandbox, runs a deepagent (text_editor + bash), reads
                       the result back. Optional SafeVerify-gated submit.
  tools.py             bash + arxiv tools. PyPantograph is invoked directly by
                       the agent from python3, not wrapped here.
  prompts.py           Instructions + task message for the agent.
  checker.py           Host-side interface to SafeVerify (the anti-cheat).
  scorer.py            Re-validates the final proof; correct iff complete proof.
  dataset.py           OEIS conjectures (theorem + sorry) -> Inspect Samples.
  task.py              The apn_oeis Inspect task.
  data/oeis/           Vendored OEIS/Auto dataset (484 files / 492 conjectures).
  lean/                Docker images + SafeVerify.
```

### How a proof search runs

1. The input is a Lean file: a sequence definition, small-term **test lemmas**,
   and a conjecture — proofs left as `sorry`.
2. `lean_prover` writes it into the sample's `default` sandbox and runs a
   `deepagent`. The agent edits the file with `text_editor` and uses `bash`
   for everything else: `import pantograph` from python3 to compile the file
   or drive interactive tactics, and the same shell as a numerical scratchpad
   (sympy/numpy). It iterates on the Lean compiler feedback until it submits.
3. The scorer independently re-validates the final file with **SafeVerify** in a
   separate trusted sandbox: every declaration (the definition, the test lemmas,
   and the conjecture) must be reproduced **verbatim**, be `sorry`-free, and use
   only permitted axioms. The kernel-level replay defends against statement
   weakening, axiom injection, and definition tampering.
4. **Gated submit (optional, `-T gated=true`):** submissions are checked by
   SafeVerify *during* the loop; a failed submission is rejected and the agent
   must keep working (until a limit), and it is told only that verification
   failed — not why — so it cannot probe SafeVerify for gaps.
5. Run several independent attempts per problem by passing `--epochs N`; each
   epoch is a fresh sample run with its own sandboxes.

## Lean sandbox

Lean runs in Docker (`apn/lean/`), matching the paper's isolated sandboxes. Each
sample gets **two** sandboxes from a shared base image:

* **`default`** — the agent's workspace (`apn-agent`):
  [PyPantograph](https://github.com/lenianiva/PyPantograph) is installed in
  the image alongside the prebuilt FormalConjectures + Mathlib oleans, so the
  agent compiles Lean by importing `pantograph` from python3 and creating a
  `Server` itself (~2s per fresh server with the page cache warm; see
  `apn/lean/Dockerfile.agent`). Also has `python3` + `sympy`/`numpy` for the
  numerical scratchpad. **No SafeVerify here.**
* **`scorer`** — a separate, trusted container (`apn-scorer`) the agent never
  writes to, where SafeVerify validates the final proof. The scorer writes the
  submitted proof (from the store) into this clean container and checks it, so
  the agent cannot tamper with the checker, the target spec, or the oleans. An
  *infrastructure* failure of SafeVerify (e.g. OOM) raises and errors the sample
  rather than being recorded as a rejection.

Each sample (and each epoch) gets its own pair of sandboxes.

**Version note.** The images pin **Lean v4.27.0** + **Mathlib v4.27.0** + the
**FormalConjectures** library — matching the paper's toolchain and the dataset
(oleans are version-specific). The agent's repl is PyPantograph `b8608f3`
(Pantograph v0.3.13, which targets Lean v4.27.0), and SafeVerify is vendored
under `apn/lean/safeverify/` (ported to Lean v4.27.0; see its `NOTICE.md`). All
three must agree to load the `.olean` files.

### Build the images

```bash
apn/lean/build.sh   # builds apn-lean-base, then apn-agent and apn-scorer
```

This clones Formal Conjectures, fetches Mathlib's prebuilt `.olean` cache
(`lake exe cache get`), and builds the FC library closure into a base image, then
layers PyPantograph (agent) and SafeVerify (scorer) on top. The images are large
(Mathlib dominates).

## Running

```bash
apn/lean/build.sh    # build the images first
inspect eval apn/task.py@apn_oeis --model openai/gpt-5.5 --token-limit 1000000
```

Each sample is an autoformalized OEIS conjecture from Formal Conjectures
(`OEIS/Auto`), vendored under `apn/data/oeis/`. `--token-limit` bounds per-problem
cost (these are open problems, so the agent will often run until the limit).
Useful flags:

- `-T names=oeis_268597_conjecture_0,...` — restrict to a subset (a smoke set).
- `-T gated=true` — SafeVerify-gated submissions (see above).
- `--epochs N` — N independent attempts per problem, each in its own sandbox.

Any Inspect-supported model works; the paper used Gemini 3.1 Pro for proving.
The first `Server.create()` in a fresh sandbox takes ~45s (Mathlib + FC load
into a `pantograph-repl`); the OS page cache makes subsequent fresh-Server
spawns ~2s, and a long-lived `Server` reused across compiles in one Python
process answers each `check_compile_async` in ~2ms.

### Running on Hawk

The package exports an Inspect registry entry point named `apn`, so Hawk can load
the task as `apn/apn_oeis` from the installed package. A smoke eval-set config is
available at `configs/example-eval-set.yml`:

```bash
hawk eval-set configs/example-eval-set.yml
```

For local Inspect runs, `apn/lean/build.sh` tags the sandbox images as
`LeanOpenProblems_<kind>_0.1.0_<git-hash>`. On Hawk, set the runner secret
`LEAN_OPEN_PROBLEMS_IMAGE_NAME` to the pushed image repository; the task
generates its compose file with the matching agent and scorer tags for the
installed package git hash.

### API keys

Provider keys live in `.env`. Inspect loads `.env` but does not override a
variable already set in the environment, so if your shell exports an empty
`OPENAI_API_KEY` (etc.) it will shadow the `.env` value. Export the key
explicitly for the run if needed:

```bash
export OPENAI_API_KEY="$(python -c "from dotenv import dotenv_values; print(dotenv_values('.env')['OPENAI_API_KEY'])")"
```

## Development

```bash
uv sync
uv run mypy        # strict type checking (Inspect ships precise types)
uv run pytest      # unit tests (no Docker or network)
```

The unit tests cover the pure logic (the scorer's verdict mapping, the daemon's
parsers, the dataset loader, prompts) with no Docker or network. The agent itself
is `deepagent`, so it is validated by running a real eval against the Lean
sandbox (above).

## Not yet implemented

- **Erdős set + `answer()`-aware scorer.** 79% of the Erdős problems use the
  `answer(...)` macro (the paper's EVOLVE-VALUE region): the solver must supply
  the *answer* as well as the proof. Auto-scoring those needs a relaxed
  statement-integrity check (only `answer(...)` spans + proof body may change),
  compilation under `set_option google.answer .withAuxiliary`, and an anti-echo
  guard — and even then genuine-answer-ness needs human confirmation (as in the
  paper). The 21% pure-proof Erdős problems are scorable as-is today.
- AlphaProof tool (tier B) — proprietary; will be a pluggable interface.
- Evolutionary population database, Elo rating, P-UCB, rater agents (tiers C/D).
- Global goal caching.
