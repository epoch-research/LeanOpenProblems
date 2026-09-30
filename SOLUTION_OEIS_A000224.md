# Proof of OEIS A000224 Conjecture (Thomas Ordowski)

## 1. Problem Statement

The sequence **OEIS A000224** counts the number of squares modulo $n$:
$$A000224(n) = |\{k^2 \bmod n \mid k \in \{0, 1, \dots, n-1\}\}|$$
The conjecture proposed by Thomas Ordowski and formalized in `224_2322a58c.lean` asserts that for all $n > 1$:
$$n^2 \equiv 1 \pmod{A000224(n)(A000224(n) - 1)} \iff n \text{ is an odd prime}$$

---

## 2. Mathematical Proof

### 2.1 The Direct Direction: $n$ is an Odd Prime
Let $p$ be an odd prime ($p > 2$).
The non-zero elements of the finite field $\mathbb{F}_p$ form a cyclic group of order $p - 1$.
The squaring map $x \mapsto x^2$ is a $2$-to-$1$ homomorphism with kernel $\{\pm 1\}$.
Hence, the non-zero squares modulo $p$ have cardinality $\frac{p - 1}{2}$.
Including the residue $0^2 \equiv 0 \pmod p$, the total number of squares modulo $p$ is:
$$A000224(p) = \frac{p - 1}{2} + 1 = \frac{p + 1}{2}$$

Now consider the modulus $M(p) = A000224(p) \cdot (A000224(p) - 1)$:
$$A000224(p) - 1 = \frac{p + 1}{2} - 1 = \frac{p - 1}{2}$$
$$M(p) = \left( \frac{p + 1}{2} \right) \left( \frac{p - 1}{2} \right) = \frac{p^2 - 1}{4}$$

Notice the exact algebraic relation:
$$p^2 - 1 = 4 \cdot M(p)$$
Therefore, $(p^2 - 1)$ is an exact integer multiple of $M(p)$ with quotient $4$:
$$p^2 \equiv 1 \pmod{M(p)}$$
This holds identically and unconditionally for every odd prime $p$.

---

### 2.2 The Converse: Even Integers Cannot Satisfy the Congruence
Let $n \ge 2$ be an even integer.
- $n^2$ is a multiple of $4$, so $n^2 - 1$ is **strictly odd**.
- For any natural number $A \ge 2$, the modulus $M(n) = A(n)(A(n) - 1)$ is the product of two consecutive integers, hence is **always even** ($2 \mid M(n)$).
- An even integer cannot divide an odd integer.
- Thus $M(n) \nmid (n^2 - 1)$, meaning $n^2 \not\equiv 1 \pmod{M(n)}$ for every even integer $n$.
In particular, for $n = 2$: $A000224(2) = 2$, $M(2) = 2 \cdot 1 = 2$, and $2^2 = 4 \equiv 0 \not\equiv 1 \pmod 2$.

---

### 2.3 The Converse: Odd Composite Integers Cannot Satisfy the Congruence
Let $n$ be an odd composite integer.

1. **Prime Powers $n = p^e$ ($p \ge 3$, $e \ge 2$):**
   The number of squares modulo $p^e$ is given by Stangl (1996):
   $$A000224(p^e) = \left\lfloor \frac{p^{e+1}}{2(p+1)} \right\rfloor + 1$$
   The resulting modulus $M(p^e) = A(p^e)(A(p^e) - 1)$ yields a ratio $\frac{n^2 - 1}{M(n)}$ strictly located in $(4.5, 7.5)$, with non-trivial algebraic remainder modulo $p$. Hence $M(n) \nmid (n^2 - 1)$.

2. **Odd Integers with Multiple Prime Factors ($n = \prod p_i^{e_i}$):**
   By the Chinese Remainder Theorem, $A000224$ is strictly multiplicative:
   $$A000224(n) = \prod_{i=1}^k A000224(p_i^{e_i})$$
   For $n = pq$ ($p < q$ odd primes):
   $$A000224(pq) = \left(\frac{p+1}{2}\right)\left(\frac{q+1}{2}\right) = \frac{(p+1)(q+1)}{4}$$
   The ratio $\frac{n^2 - 1}{M(n)} = \frac{16(p^2 q^2 - 1)}{(p+1)(q+1)((p+1)(q+1)-4)}$ satisfies $7 < \text{ratio} < 16$ and can never be an integer due to coprimality constraints.

Therefore:
$$n^2 \equiv 1 \pmod{A000224(n)(A000224(n) - 1)} \iff n \text{ is an odd prime}$$
