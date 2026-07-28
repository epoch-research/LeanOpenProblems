/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 897

*References:*
- [erdosproblems.com/897](https://www.erdosproblems.com/897)
- [Ar25] Archivara Math Research Agent, [An Additive Counterexample: Erdős Problem 897](https://archivara.org/paper/df04f023-6ef0-4c52-bd12-18cdaa8f0741) (2025)
- [ArWu25] Aristotle, operated mostly by L. Wu, [Lean formalisation of Erdős problem 897](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos897.lean) (2025)
- [Wi70] E. Wirsing, A characterization of $\log n$ as an additive arithmetic function.
  Symposia Math. (1970), 45-57.
- [Wi81] E. Wirsing, Additive and completely additive functions with restricted growth.
  Recent progress in analytic number theory, Vol. 2 (Durham, 1979), 231--280 (1981).
-/
-- TODO(lezeau): add `ArithmeticFunction.IsAdditive` to `ForMathlib`

namespace Erdos897

/--
Let $f(n)$ be an additive function (so that $f(ab)=f(a)+f(b)$
if $(a,b)=1$) such that $\limsup_{p,k} f(p^k) / \log(p^k) = ∞$ and $f(p^k) = f(p)$
or $f(p^k) = kf(p)$.
Is it true that $\limsup_n (f(n+1)−f(n))/ \log n = ∞$?

The known counterexample does not satisfy either of these extra hypotheses, so this variant remains
open.
-/
theorem erdos_897.variants.parts.i : ∀ (f : ℕ → ℝ),
    (∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b) →
    ((Filter.atTop ⊓ Filter.principal {(p, k) : ℕ × ℕ | p.Prime}).limsup
      (fun (p, k) => (f (p^k) / (p^k : ℝ).log : EReal)) = ⊤) →
    (∀ k p, p.Prime → f (p^k) = f p) ∨ (∀ (k p : ℕ), p.Prime → f (p^k) = k*f p) →
    Filter.atTop.limsup (fun (n : ℕ) => ((f (n+1) - f n) / (n : ℝ).log : EReal)) = ⊤ := by
  sorry

end Erdos897
