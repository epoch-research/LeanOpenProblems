This project evaluates whether AI language models can resolve conjectures stated in Lean. The intent is to use it on mathematical conjectures that are open (ones were no proof is known, even in natural language), hence the name of the repo. But the code could be applied to any Lean statement.   

It is built on the [Inspect](https://inspect.aisi.org.uk/) evaluation framework.

An agent is given a conjecture and asked to prove or disprove it. A submission counts only if it passes [Comparator](https://github.com/leanprover/comparator), the Lean FRO's adversarially robust proof checker. The agent works in one sandboxed container, and comparator runs in a separate one. This setup defeats many classes of attacks (see Section 3.3 of [Adamczewski and Bloom (2026)](https://arxiv.org/abs/2609.25050)) 

Most conjectures come from [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures), Google DeepMind's open-source library of formalized open problems, though other sources are supported too.

Evaluations can be run at scale with [Hawk](https://github.com/METR/hawk).

## Benchmarks based on this repo
* [FrontierMath Erdős](https://arxiv.org/abs/2609.25050)
* [OEIS Open](https://arxiv.org/abs/2608.11941)

