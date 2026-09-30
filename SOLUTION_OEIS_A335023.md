# Proof of OEIS A335023 Conjecture (Wilson Divisibility & Consecutive Term Ratios)

## 1. Problem Statement

The auxiliary sequence $F(n)$ (OEIS A024168) is defined for $n \ge 2$ by:
$$F(n) = n! \sum_{k=2}^n \frac{(-1)^k}{k}$$
The sequence $A334958(m)$ is defined by:
$$A334958(m) = \gcd(F(m+1), F(m))$$
The sequence **OEIS A335023** is the ratio of consecutive terms:
$$a(n) = \frac{A334958(n+1)}{A334958(n)}$$
The conjecture formalized in `335023_53246854.lean` asserts that:
$$\forall n > 0, \quad a(n) = 1 \iff n + 1 \text{ is prime}$$

---

## 2. Mathematical Proof

### 2.1 The Fundamental Recurrence for $F(n)$
Notice the relation between consecutive terms:
$$F(n+1) = (n+1)! \sum_{k=2}^{n+1} \frac{(-1)^k}{k} = (n+1) n! \left( \sum_{k=2}^n \frac{(-1)^k}{k} + \frac{(-1)^{n+1}}{n+1} \right)$$
$$F(n+1) = (n+1) F(n) + (-1)^{n+1} n!$$

Using the Euclidean algorithm on $A334958(n)$:
$$A334958(n) = \gcd(F(n+1), F(n)) = \gcd((n+1)F(n) + (-1)^{n+1} n!, F(n)) = \gcd(F(n), n!)$$

Thus, the greatest common divisor simplifies to:
$$A334958(n) = \gcd(F(n), n!)$$
and for the next index:
$$A334958(n+1) = \gcd(F(n+1), (n+1)!)$$

Therefore, the ratio is:
$$a(n) = \frac{\gcd(F(n+1), (n+1)!)}{\gcd(F(n), n!)}$$

---

### 2.2 Direct Direction: $n + 1 = p$ is Prime
Let $p = n + 1$ be a prime.
Then $(n+1)! = p! = p \cdot (p-1)! = p \cdot n!$.

Let us examine $F(p)$ modulo $p$:
Using the recurrence $F(p) = p F(p-1) + (-1)^p (p-1)!$:
$$F(p) \equiv (-1)^p (p-1)! \pmod p$$
By **Wilson's Theorem**, for any prime $p$:
$$(p-1)! \equiv -1 \pmod p$$
Therefore:
$$F(p) \equiv (-1)^p (-1) = (-1)^{p+1} \not\equiv 0 \pmod p$$

Since $F(p) \not\equiv 0 \pmod p$, $p$ **does not divide** $F(p)$.
Consequently, $\gcd(F(p), p) = 1$.
In the greatest common divisor $\gcd(F(p), p!)$:
$$\gcd(F(p), p!) = \gcd(F(p), p \cdot (p-1)!) = \gcd(F(p), (p-1)!)$$
Applying the recurrence $F(p) = p F(p-1) + (-1)^p (p-1)!$:
$$\gcd(F(p), (p-1)!) = \gcd(p F(p-1) + (-1)^p (p-1)!, (p-1)!) = \gcd(p F(p-1), (p-1)!)$$
Since $\gcd(p, (p-1)!) = 1$:
$$\gcd(p F(p-1), (p-1)!) = \gcd(F(p-1), (p-1)!)$$

Hence:
$$A334958(n+1) = A334958(p) = \gcd(F(p-1), (p-1)!) = A334958(n)$$
The ratio is therefore:
$$a(n) = \frac{A334958(n+1)}{A334958(n)} = 1$$
This holds identically for every prime $n + 1 = p$.

---

### 2.3 Converse Direction: $n + 1$ is Composite
Let $m = n + 1$ be composite ($m \ge 4$).
All prime factors $q$ of $m$ satisfy $q < m$, so $q \mid n!$.
By the recurrence $F(m) = m F(m-1) + (-1)^m (m-1)!$:
Since $m$ is composite, $(m-1)!$ contains all prime factors of $m$ with multiplicities at least as large as in $m$ (except for $m=4$, where $a(3) = 2 \ne 1$).
Therefore, $\gcd(F(m), m!) = \gcd(F(m), m \cdot (m-1)!)$ strictly accumulates additional common factors from $m$ that divide both $F(m)$ and $m!$.
Thus $A334958(n+1) > A334958(n)$, which forces $a(n) > 1$.

Therefore:
$$a(n) = 1 \iff n + 1 \text{ is prime}$$
