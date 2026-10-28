# Wikipedia research-open: pre-release model

The `apn_wikipedia` dataset runs on OpenAI's pre-release model `aurora-alpha-bio-cyber-capabilities`. The dataset is every `research open` statement in FC's `FormalConjectures/Wikipedia` at FC main as of 2026-10-28 (`5a2fb850`): 273 runnable samples. The run uses the deep agent with literature and `reasoning_effort: max`, $1,000 per sample, and a 4-day `working_limit`. Failures are handled with `retry_on_error: 16` and no checkpointing, as in the `bloom68-scaling-predep` epoch arm.

| Config | Samples | Per-sample budget | `working_limit` |
|---|---|---|---|
| `wikipedia-aurora-smoke.yaml` | 2 | $20 | 2h |
| `wikipedia-aurora.yaml` | 273 | $1,000 | 4 days |

Model access and pricing are the same as in `bloom68-scaling-predep`. The `epoch` provider comes from epoch-research/benchmarks `e60b6bb0c7306ac66d8b6e0873d96300d4eb9572`, called at `api.openai.com` with the IP-locked predeployment key, so runs only work from Hawk. Aurora's prices aren't published, so GPT-6 Astra's are assumed.

Pins: LeanOpenProblems `c6c86cba9b7c95d50b40021281f68e7f844b3624` on branch `2026-10-28-wikipedia-predep`. That branch is `509ee49` (the commit `bloom68-scaling-predep` pins) plus the Wikipedia dataset commits from `2026-10-28-wikipedia`. The provider pins `inspect-ai==0.3.273`, but main's inspect-swarm needs 0.3.283 or later, so the dataset can't run from main. The dataset files are identical on both branches.

## Launching

The run bills `OPENAI_API_KEY_PREDEP`, passed to Hawk as `OPENAI_API_KEY`:

```bash
set -a; source .env; set +a
OPENAI_API_KEY="$OPENAI_API_KEY_PREDEP" PYTHON_KEYRING_BACKEND=keyrings.alt.file.PlaintextKeyring \
  .venv/bin/hawk eval-set configs/wikipedia-predep/wikipedia-aurora.yaml \
  --secret OPENAI_API_KEY --secret ANTHROPIC_API_KEY --secret GOOGLE_API_KEY --secret LEAN_OPEN_PROBLEMS_IMAGE_NAME
```

## Log

Dates and times are UTC.

- **2026-10-28 20:03 (smoke test):** Launched `wiki-aurora-smoke-udvzsih0qv0owsd3` (`wikipedia-aurora-smoke.yaml`): `AmicableNumbers.infinitely_many_amicable` and `Hadamard.HadamardConjecture.variants.«167»`. Launched before the pin's `agent_corpus` images had finished building in CI (run 40753096134).
