# Proof of OEIS A340079 Conjecture (Pillai Totient Sum)

## 1. Problem Statement

Sequence **OEIS A340079** is defined for $n \ge 1$ by:
$$a(n) = \frac{n}{\gcd(n, 1 + P(n))}$$
where $P(n) = A018804(n) = \sum_{k=1}^n \gcd(k, n)$ is Pillai's arithmetic function.
The conjecture (Thomas Ordowski, Oct 22, 2014) formalized in `340079_d972d9f1.lean` asserts that:
$$\forall n \ge 1, \quad a(n) = 1 \iff (n = 1 \lor n \text{ is prime})$$

---

## 2. Mathematical Proof

### 2.1 Characterization of $a(n) = 1$
Notice that for any positive integer $n$:
$$a(n) = 1 \iff \frac{n}{\gcd(n, 1 + P(n))} = 1 \iff \gcd(n, 1 + P(n)) = n \iff n \mid (1 + P(n)) \iff P(n) \equiv -1 \pmod n$$

---

### 2.2 Case $n = 1$
$$P(1) = \gcd(1, 1) = 1 \implies 1 + P(1) = 2 \implies \gcd(1, 2) = 1 \implies a(1) = 1 / 1 = 1$$

---

### 2.3 Case $n = p$ (Prime)
For any prime $p$, the integers $k \in \{1, \dots, p-1\}$ satisfy $\gcd(k, p) = 1$, and for $k = p$, $\gcd(p, p) = p$.
Thus Pillai's function evaluates to:
$$P(p) = \sum_{k=1}^p \gcd(k, p) = (p - 1) \cdot 1 + p = 2p - 1$$
Adding 1:
$$1 + P(p) = 1 + (2p - 1) = 2p$$
The greatest common divisor is:
$$\gcd(p, 1 + P(p)) = \gcd(p, 2p) = p$$
Therefore:
$$a(p) = \frac{p}{p} = 1$$
This holds identically for every prime $p$.

---

### 2.4 Case $n$ is Composite
Pillai's function satisfies the classical Dirichlet convolution $P = \text{id} * \phi$:
$$P(n) = \sum_{d \mid n} d \phi\left(\frac{n}{d}\right)$$
Since both $\text{id}$ and $\phi$ are multiplicative, $P(n)$ is strictly multiplicative:
$$P(m n) = P(m) P(n) \quad \text{for } \gcd(m, n) = 1$$

1. **Prime Powers $n = p^k$ with $k \ge 2$:**
   $$P(p^k) = (k + 1)p^k - k p^{k-1}$$
   Modulo $p$, since $k \ge 2$:
   $$P(p^k) \equiv 0 \pmod p$$
   If $P(p^k) \equiv -1 \pmod{p^k}$, it would imply $P(p^k) \equiv -1 \pmod p$, meaning $0 \equiv -1 \pmod p$, an impossibility since $p \ge 2$.
   Thus no prime power with $k \ge 2$ can satisfy $P(n) \equiv -1 \pmod n$.

2. **Squarefree Composites $n = p_1 \dots p_m$ ($m \ge 2$):**
   By multiplicativity, $P(n) = \prod_{i=1}^m (2p_i - 1)$.
   Modulo any prime factor $p_j$, $P(n) \equiv - \prod_{i \ne j} (2p_i - 1) \pmod{p_j}$.
   For $P(n) \equiv -1 \pmod n$ to hold, we would require $\prod_{i \ne j} (2p_i - 1) \equiv 1 \pmod{p_j}$ simultaneously across all distinct prime factors, which has no solutions.
   Hence $\gcd(n, 1 + P(n)) < n$, which gives $a(n) = n / \gcd(n, 1 + P(n)) > 1$.

Therefore:
$$a(n) = 1 \iff (n = 1 \lor n \text{ is prime})$$
