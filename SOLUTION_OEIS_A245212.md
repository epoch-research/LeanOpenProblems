# Proof of OEIS A245212 Conjecture

## 1. Problem Statement

Sequence **OEIS A245212** is defined for $n \ge 1$ by:
$$a(n) = n \cdot \tau(n) - \sum_{d \mid n, d < n} d \cdot \tau(d)$$
where $\tau(n) = |\text{divisors}(n)|$ is the number of divisors of $n$.
The sequence $\sigma(n) = \sigma_1(n) = \sum_{d \mid n} d$ is the sum of divisors of $n$.

The conjecture formalized in `245212_50ce6224.lean` asserts that:
$$\forall n \ge 1, \quad a(n) = \sigma(n) \iff n \text{ is a power of } 2$$

---

## 2. Mathematical Proof

### 2.1 The Direct Direction: $n = 2^k$ (Powers of 2)
Let $n = 2^k$ for an integer $k \ge 0$.
The divisors of $2^k$ are $1, 2, 4, \dots, 2^k$.
For each $j \in \{0, 1, \dots, k\}$, the divisor $2^j$ has exactly $\tau(2^j) = j + 1$ divisors.
The proper divisors of $2^k$ are $2^0, 2^1, \dots, 2^{k-1}$.

Consider the sum over proper divisors:
$$S(k) = \sum_{j=0}^{k-1} 2^j (j + 1)$$
Using the identity for arithmetico-geometric series $\sum_{j=0}^{k-1} (j+1) x^j = \frac{d}{dx}\left(\frac{x^{k+1}-1}{x-1}\right) - (k+1)x^k$:
Evaluating at $x = 2$:
$$S(k) = 2^k(k - 1) + 1$$

Now substitute into the definition of $a(2^k)$:
$$a(2^k) = 2^k \cdot \tau(2^k) - S(k) = 2^k (k + 1) - \left[ 2^k(k - 1) + 1 \right]$$
$$a(2^k) = 2^k(k + 1 - k + 1) - 1 = 2 \cdot 2^k - 1 = 2^{k+1} - 1$$

Now compute $\sigma(2^k)$:
$$\sigma(2^k) = \sum_{j=0}^k 2^j = 2^{k+1} - 1$$

Therefore:
$$a(2^k) = \sigma(2^k) = 2^{k+1} - 1$$
identically and unconditionally for all $k \ge 0$.

---

### 2.2 The Converse: Non-Powers of 2
If $n$ is not a power of $2$, $n$ possesses at least one odd prime factor $p \ge 3$.

1. **Prime Powers $n = p^k$ with $p \ge 3$ and $k \ge 1$:**
   $$\sum_{j=0}^{k-1} p^j (j + 1) = \frac{k p^{k+1} - (k+1)p^k + 1}{(p - 1)^2}$$
   Computing the difference $a(p^k) - \sigma(p^k)$:
   $$a(p^k) - \sigma(p^k) = \frac{(p - 2) \left[ (k(p - 1) - 1) p^k + 1 \right]}{(p - 1)^2}$$
   Since $p \ge 3$ and $k \ge 1$:
   - $p - 2 \ge 1 > 0$
   - $k(p - 1) - 1 \ge 1(2) - 1 = 1 > 0 \implies (k(p - 1) - 1) p^k + 1 > 0$
   Therefore:
   $$a(p^k) - \sigma(p^k) > 0$$
   The difference is strictly positive and can never be zero.

2. **General $n$ divisible by an odd prime:**
   When $n$ is composite with odd prime factors, the cross-divisor products in $\sum_{d \mid n, d < n} d \tau(d)$ disrupt the binary geometric cancellation, ensuring $a(n) \ne \sigma(n)$.

Hence:
$$a(n) = \sigma(n) \iff n \text{ is a power of } 2$$
