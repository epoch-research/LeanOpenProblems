"""AlphaProof Nexus, reimplemented on top of Inspect.

This package is an open reimplementation of the agent framework described in
Tsoukalas et al., *Advancing Mathematics Research with AI-Driven Formal Proof
Search* (arXiv:2605.22763v1). It builds LLM-driven Lean proof-search agents as
Inspect evaluations.

The framework describes four agent tiers built on a shared generation/validation
pipeline:

* **(A) basic** -- independent "Ralph-loop" prover subagents that refine a Lean
  proof sketch with a ``search_replace`` tool, guided by Lean compiler feedback.
* **(B)** = A plus an AlphaProof proof tool.
* **(C)** = A plus an evolutionary population database (Plackett-Luce Elo via
  Gibbs sampling, Thompson sampling, P-UCB selection, LLM rater agents).
* **(D) full-featured** = A + AlphaProof + evolution.

This module currently implements tier (A); the remaining tiers are layered on
top in later work.
"""

__all__ = ["__version__"]

__version__ = "0.1.0"
