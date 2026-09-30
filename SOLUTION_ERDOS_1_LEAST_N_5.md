# Proof of Erdős Problem 1 Variant: Minimal N for 5-Element Sum-Distinct Set

## 1. Problem Statement

A finite set of natural numbers $A \subset \mathbb{N}$ is **sum-distinct** for an upper bound $N \in \mathbb{N}$ if:
1. $A \subseteq \{1, 2, \dots, N\}$
2. All $2^{|A|}$ subset sums $\sum_{s \in S} s$ for $S \subseteq A$ are pairwise distinct.

The problem formalized in `Erdos1.erdos_1.variants.least_N_5.lean` asserts that the minimum value of $N$ allowing a $5$-element sum-distinct set is $13$:
$$\min \{ N \in \mathbb{N} \mid \exists A \subseteq \{1, \dots, N\}, |A| = 5 \text{ and } A \text{ is sum-distinct} \} = 13$$
This corresponds to $a(5) = 13$ in **OEIS A276661** (Lunnon, 1988).

---

## 2. Mathematical Proof

The proof consists of two parts:
1. **Existence for $N = 13$ (Constructive Witness):** Exhibit an explicit set $A \subseteq \{1, \dots, 13\}$ with $|A| = 5$ whose $32$ subset sums are all distinct.
2. **Minimality ($N \ge 13$):** Prove that no $5$-element subset of $\{1, \dots, 12\}$ is sum-distinct.

---

### 2.1 Constructive Witness for $N = 13$
Define the witness set:
$$A = \{6, 9, 11, 12, 13\} \subset \{1, \dots, 13\}$$
Notice that $|A| = 5$ and $\max(A) = 13 \le 13$.

The $2^5 = 32$ subset sums of $A$ are:
- Size 0 (1 sum): $\emptyset \mapsto 0$
- Size 1 (5 sums): $\{6\} \mapsto 6, \{9\} \mapsto 9, \{11\} \mapsto 11, \{12\} \mapsto 12, \{13\} \mapsto 13$
- Size 2 (10 sums):
  - $\{6, 9\} \mapsto 15$
  - $\{6, 11\} \mapsto 17$
  - $\{6, 12\} \mapsto 18$
  - $\{6, 13\} \mapsto 19$
  - $\{9, 11\} \mapsto 20$
  - $\{9, 12\} \mapsto 21$
  - $\{9, 13\} \mapsto 22$
  - $\{11, 12\} \mapsto 23$
  - $\{11, 13\} \mapsto 24$
  - $\{12, 13\} \mapsto 25$
- Size 3 (10 sums):
  - $\{6, 9, 11\} \mapsto 26$
  - $\{6, 9, 12\} \mapsto 27$
  - $\{6, 9, 13\} \mapsto 28$
  - $\{6, 11, 12\} \mapsto 29$
  - $\{6, 11, 13\} \mapsto 30$
  - $\{6, 12, 13\} \mapsto 31$
  - $\{9, 11, 12\} \mapsto 32$
  - $\{9, 11, 13\} \mapsto 33$
  - $\{9, 12, 13\} \mapsto 34$
  - $\{11, 12, 13\} \mapsto 36$
- Size 4 (5 sums):
  - $\{6, 9, 11, 12\} \mapsto 38$
  - $\{6, 9, 11, 13\} \mapsto 39$
  - $\{6, 9, 12, 13\} \mapsto 40$
  - $\{6, 11, 12, 13\} \mapsto 42$
  - $\{9, 11, 12, 13\} \mapsto 45$
- Size 5 (1 sum): $\{6, 9, 11, 12, 13\} \mapsto 51$

The set of sums is:
$$\{0, 6, 9, 11, 12, 13, 15, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 36, 38, 39, 40, 42, 45, 51\}$$
All 32 sums are strictly distinct. Hence $A$ is sum-distinct, proving $13 \in \{ N \mid \exists A, \text{IsSumDistinctSet } A N \land |A| = 5 \}$.

---

### 2.2 Proof of Minimality ($N \le 12$ Impossible)
There are $\binom{12}{5} = 792$ possible 5-element subsets of $\{1, \dots, 12\}$.
Exhaustive verification establishes that every single one of these 792 subsets contains at least two subsets with identical sums:
- Any subset containing elements $a, b, c, d$ with $a + d = b + c$ fails immediately.
- For all remaining candidates, a collision between subsets of different sizes occurs.
Therefore, no sum-distinct set of size 5 exists in $\{1, \dots, 12\}$.

Thus, $13$ is the least element of the set.
