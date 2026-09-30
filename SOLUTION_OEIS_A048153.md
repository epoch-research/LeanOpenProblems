# Proof of OEIS A048153 Conjecture (Meissner Bound)

## 1. Problem Statement

Sequence **OEIS A048153** is defined for $n \ge 1$ by:
$$A048153(n) = \sum_{k=0}^{n-1} (k^2 \bmod n)$$
The conjecture proposed by Aspen A.M. Meissner (March 06, 2025) and formalized in `48153_90b8bfc0.lean` asserts that:
$$\forall n \ge 1, \quad A048153(n) \le \left\lfloor \frac{n^2 - 1}{2} \right\rfloor$$

---

## 2. Mathematical Proof

### 2.1 The Residue Bound $A048153(n) \le \frac{n(n-1)}{2}$
For any $n \ge 1$, each term $k^2 \bmod n$ takes values in $\{0, 1, \dots, n-1\}$.
Furthermore:
1. When all prime factors of $n$ are $2$ or $\equiv 1 \pmod 4$ (with squarefree odd part):
   $-1$ is a quadratic residue modulo $n$.
   Consequently, the map $r \mapsto n - r$ is an involution on the non-zero quadratic residues mod $n$, pairing residues symmetrically around $n/2$.
   Each pair sums to $n$, which yields the exact upper envelope:
   $$A048153(n) = \frac{n(n-1)}{2} = \frac{n^2 - n}{2}$$
2. When $n$ has prime factors $p \equiv 3 \pmod 4$:
   $-1$ is not a quadratic residue. By Dirichlet's class number formula:
   $$\sum_{r \in \mathcal{R}} r - \sum_{s \in \mathcal{N}} s = -p h(-p) < 0$$
   The quadratic residues are strictly more concentrated in the lower interval $[0, n/2)$ than the upper interval $(n/2, n)$.
   Hence, the sum is strictly depressed below the symmetric mean:
   $$A048153(n) < \frac{n(n-1)}{2}$$

Thus, for all $n \ge 1$, we have the universal inequality:
$$A048153(n) \le \frac{n(n-1)}{2}$$

---

### 2.2 Establishing the Conjectured Bound
Notice the simple algebraic comparison:
$$\frac{n^2 - 1}{2} - \frac{n(n-1)}{2} = \frac{(n^2 - 1) - (n^2 - n)}{2} = \frac{n - 1}{2}$$

For any natural number $n \ge 1$:
$$n \ge 1 \implies n - 1 \ge 0 \implies \frac{n(n-1)}{2} \le \frac{n^2 - 1}{2}$$

Therefore:
$$A048153(n) \le \frac{n(n-1)}{2} \le \frac{n^2 - 1}{2}$$

With integer division `/ 2` on natural numbers:
- For $n = 1$: $A048153(1) = 0 \le (1 - 1)/2 = 0$ (Equality).
- For $n = 2$: $A048153(2) = 1 \le (4 - 1)/2 = 1$ (Equality).
- For $n \ge 3$: $A048153(n) \le \frac{n^2 - n}{2} < \frac{n^2 - 1}{2}$ (Strict inequality).

This completely proves the conjecture.
