<!-- Vendored from https://github.com/mkauers/ore_algebra at rev 18680180c884fac869a064db99f29a221aad9dfe: README.md plus docstrings extracted from ore_algebra.py, guessing.py, ore_operator_1_1.py, differential_operator_1_1.py, recurrence_operator_1_1.py -->

# ore_algebra (Sage package)

Ore algebra
============

https://github.com/mkauers/ore_algebra/

Description
-----------

A Sage implementation of Ore algebras, Ore polynomials, and differentially
finite functions

Main features for the most common algebras include basic arithmetic and actions;
gcrd and lclm; D-finite closure properties; creative telescoping; natural
transformations between related algebras; guessing; desingularization; solvers
for polynomials, rational functions and (generalized) power series. Univariate
differential operators also support the numerical computation of analytic
solutions with rigorous error bounds and related features.



## Module `ore_algebra` — constructing Ore algebras

Ore algebras

The ``ore_algebra`` package provides functionality for doing computations with Ore polynomials.

Ore polynomials are operators which can be used to describe special functions or combinatorial
sequences. Typical examples are linear differential operators with polynomial coefficients.

Ore polynomials are elements of Ore algebras. Ore algebras are ring objects created by the
function ``OreAlgebra`` as described below.

Depending on the particular parent algebra, Ore polynomials may support different functionality.
For example, for Ore polynomials representing recurrence operators, there is a method for
computing interlacing operators, an operation which does not make sense for differential operators.

The typical user will only need two functions defined in the package:

 * ``OreAlgebra`` -- for creating a new Ore algebra object.
 * ``guess`` -- for fitting an Ore polynomial to a given set of data.

Ore polynomials are created using ``OreAlgebra`` objects, and most of the functionality for
doing calculations with Ore polynomials is available in the methods attached to them.

For examples and further information, see the docstring of ``OreAlgebra`` below, or the
tutorial paper *Ore Polynomials in Sage* by the authors.


AUTHOR:

- Manuel Kauers, Maximilian Jaroschek, Fredrik Johansson (2013-06-15)

### `OreAlgebra`

```
An Ore algebra is a noncommutative polynomial ring whose elements are
interpreted as operators.

An Ore algebra has the form `A=R[\partial_1,\partial_2,\dots,\partial_n]`
where `R` is an integral domain and `\partial_1,\dots,\partial_n` are
indeterminates.  For each of them, there is an associated automorphism
`\sigma:R\\rightarrow R` and a skew-derivation `\delta:R\\rightarrow R`
satisfying `\delta(a+b)=\delta(a)+\delta(b)` and
`\delta(ab)=\delta(a)b+\sigma(a)\delta(b)` for all `a,b\in R`.

The generators `\partial_i` commute with each other, but not with elements
of the base ring `R`. Instead, we have the commutation rules `\partial u =
\sigma(u) \partial + \delta(u)` for all `u\in R`.

The base ring `R` must be suitable according to the following definition:
`ZZ`, `QQ`, `GF(p)` for primes `p`, and finite algebraic extensions of `QQ`
are suitable, and if `R` is suitable then so are `R[x]`, `R[x_1,x_2,...]`
and `Frac(R)`. It is assumed that all the `\sigma` leave ``R.base_ring()`` fixed
and all the `\delta` map ``R.base_ring()`` to zero.

A typical example of an Ore algebra is the ring of linear differential
operators with rational function coefficients in one variable,
e.g. `A=QQ[x][D]`. Here, `\sigma` is the identity and `\delta` is the
standard derivation `d/dx`.

To create an Ore algebra, supply a suitable base ring and one or more
generators. Each generator has to be given in form of a triple
``(name,sigma,delta)`` where ``name`` is the desired name of the variable
(used for printout), ``sigma`` and ``delta`` are arbitrary callable objects
which applied to the base ring return other base ring elements in accordance
with the relevant laws. It is not checked whether they do.

::

    sage: from ore_algebra import *

    sage: R.<x> = QQ['x']
    sage: K = R.fraction_field()

    # This creates an Ore algebra of linear differential operators
    sage: A.<D> = OreAlgebra(K, ('D', lambda p: p, lambda p: p.derivative(x)))
    sage: A
    Univariate Ore algebra in D over Fraction Field of Univariate Polynomial Ring in x over Rational Field

    # This creates an Ore algebra of linear recurrence operators
    sage: A.<S> = OreAlgebra(K, ('S', lambda p: p(x+1), lambda p: K.zero()))
    sage: A
    Univariate Ore algebra in S over Fraction Field of Univariate Polynomial Ring in x over Rational Field

Instead of a callable object for `\sigma` and `\delta`, also a dictionary can
be supplied which for every generator of the base ring specifies the desired
image. If some generator is not in the dictionary, it is understood that
`\sigma` acts as identity on it, and that `\delta` maps it to zero.

::

    sage: U.<x, y> = ZZ['x', 'y']

    # here, the base ring represents the differential field QQ(x, e^x)
    sage: A.<D> = OreAlgebra(U, ('D', {}, {x:1, y:y}))

    # here, the base ring represents the difference field QQ(x, 2^x)
    sage: B.<S> = OreAlgebra(U, ('S', {x:x+1, y:2*y}, {}))

    # here too, but the algebra's generator represents the forward difference instead of the shift
    sage: C.<Delta> = OreAlgebra(U, ('Delta', {x:x+1, y:2*y}, {x:1, y:y}))

For the most frequently needed operators, the constructor accepts their
specification as a string only, without explicit statement of sigma or
delta. The string has to start with one of the letters listed in the
following table. The remainder of the string has to be the name of one
of the generators of the base ring. The operator will affect this generator
and leave the others untouched.

   ============= ======================= ================ =============
   Prefix        Operator                `\sigma`         `\delta`
   ============= ======================= ================ =============
   C             Commutative variable    `\{\}`           `\{\}`
   D             Standard derivative     `\{\}`           `\{x:1\}`
   S             Standard shift          `\{x:x+1\}`      `\{\}`
   \u0394, F          Forward difference      `\{x:x+1\}`      `\{x:1\}`
   \u03B8, T, E       Euler derivative        `\{\}`           `\{x:x\}`
   Q             q-shift                 `\{x:q*x\}`      `\{\}`
   J             Jackson's q-derivative  `\{x:q*x\}`      `\{x:1\}`
   ============= ======================= ================ =============

In the case of C, the suffix need not be a generator of the ground field but
may be an arbitrary string. In the case of Q and J, either the base ring has
to contain an element `q`, or the base ring element to be used instead has to
be supplied as optional argument.

::

    sage: R.<x, y> = QQ['x', 'y']
    sage: A = OreAlgebra(R, 'Dx') # This creates an Ore algebra of differential operators
    sage: A == OreAlgebra(R, ('Dx', {}, {x:1}))
    True
    sage: A == OreAlgebra(R, ('Dx', {}, {y:1})) # the Dx in A acts on x, not on y
    False

    # This creates an Ore algebra of linear recurrence operators
    sage: A = OreAlgebra(R, 'Sx')
    sage: A == OreAlgebra(R, ('Sx', {x:x+1}, {}))
    True
    sage: A == OreAlgebra(R, ('Sx', {y:y+1}, {})) # the Sx in A acts on x, not on y
    False
    sage: OreAlgebra(R, 'Qx', q=2)
    Univariate Ore algebra in Qx over Multivariate Polynomial Ring in x, y over Rational Field

A generator can optionally be extended by a vector `(w_0,w_1,w_2)` of
base ring elements which encodes the product rule for the generator:
`D(u*v) == w_0*u*v + w_1*(D(u)*v + u*D(v)) + w_2*D(u)*D(v)`. This data
is needed in the computation of symmetric products.

Ore algebras support coercion from their base rings. Furthermore, an Ore
algebra `A` knows how to coerce commutative polynomials `p` to elements of
`A` if the generators of the parent of `p` have the same names as the
generators of `A`, and the base ring of the parent of `p` admits a coercion
to the base ring of `A`. The ring of these polynomials is called the
associated commutative algebra of `A`, and it can be obtained by calling
``A.associated_commutative_algebra()``.

Elements of Ore algebras are called Ore operators. They can be constructed
from the same data from which also elements of the associated commutative
algebra can be constructed.

The conversion from data to an Ore operator is equivalent to the conversion
from the given data to an element of the associated commutative algebra, and
from there to an Ore operator. This has the consequence that possible implicit
information about multiplication order may be lost, for example when generating
operators from strings:

::

    sage: A = OreAlgebra(QQ['x'], 'Dx')
    sage: A("Dx*x")
    x*Dx
    sage: A("Dx")*A("x")
    x*Dx + 1

A safer way of creating operators is via a list of coefficients. These are then
always interpreted as standing to the left of the respective algebra generator monomial.

::

    sage: R.<x> = QQ['x']
    sage: A.<Dx> = OreAlgebra(R, 'Dx')
    sage: A([x^2+1, 5*x-7, 7*x+18])
    (7*x + 18)*Dx^2 + (5*x - 7)*Dx + x^2 + 1
    sage: (7*x + 18)*Dx^2 + (5*x - 7)*Dx + x^2 + 1
    (7*x + 18)*Dx^2 + (5*x - 7)*Dx + x^2 + 1
    sage: _^2
    (49*x^2 + 252*x + 324)*Dx^4 + (70*x^2 + 180*x)*Dx^3 + (14*x^3 + 61*x^2 + 49*x + 216)*Dx^2 + (10*x^3 + 14*x^2 + 107*x - 49)*Dx + x^4 + 12*x^2 + 37

    sage: R.<x> = QQ['x']
    sage: A.<Sx> = OreAlgebra(QQ['x'], 'Sx')
    sage: A([x^2+1, 5*x-7, 7*x+18])
    (7*x + 18)*Sx^2 + (5*x - 7)*Sx + x^2 + 1
    sage: (7*x + 18)*Sx^2 + (5*x - 7)*Sx + x^2 + 1
    (7*x + 18)*Sx^2 + (5*x - 7)*Sx + x^2 + 1
    sage: _^2
    (49*x^2 + 350*x + 576)*Sx^4 + (70*x^2 + 187*x - 121)*Sx^3 + (14*x^3 + 89*x^2 + 69*x + 122)*Sx^2 + (10*x^3 - 4*x^2 + x - 21)*Sx + x^4 + 2*x^2 + 1

It is possible to bypass the check that the base ring is suitable, but doing so
may lead to mathematically incorrect results. Only use this if you know exactly
what you are doing! ::

    sage: R.<x> = SR[]
    sage: Dop.<Dx> = OreAlgebra(R, check_base_ring=False)
    sage: (Dx - pi*x)^2
    Dx^2 - 2*pi*x*Dx + pi^2*x^2 - pi
```


### `DifferentialOperators`

```
Shorthand to construct an Ore algebra of differential operators.

Return an Ore algebra of differential operators with polynomial
coefficients, along with objects representing, x and d/dx.

.. SEEALSO:: :func:`OreAlgebra`

INPUT:

* ``base`` (default ``QQ``) - base ring of the polynomial coefficients
* ``var`` (default ``x``) - variable name

EXAMPLES::

    sage: from ore_algebra import *
    sage: Dops, x, Dx = DifferentialOperators()
    sage: Dops
    Univariate Ore algebra in Dx over Univariate Polynomial Ring in x over
    Rational Field
    sage: x*Dx + 1
    x*Dx + 1

    sage: DifferentialOperators(GF(2), 't')
    (Univariate Ore algebra in Dt over Univariate Polynomial Ring in t over
    Finite Field of size 2 (...),
    t, Dt)
```


## Module `ore_algebra.guessing`

Guessing tools

TESTS::

    sage: from ore_algebra import OreAlgebra, guess
    sage: guess([SR(1/(i+1)) for i in range(10)], OreAlgebra(QQ['n'], 'Sn'))
    (-n - 2)*Sn + n + 1

### `guess_rec`

```
Shortcut for ``guess`` applied with an Ore algebra of shift operators in `S` over `K[n]`
where `K` is the parent of ``data[0]``.

See the docstring of ``guess`` for further information.
```


### `guess_deq`

```
Shortcut for ``guess`` applied with an Ore algebra of differential operators in `D` over `K[x]`
where `K` is the parent of ``data[0]``.

See the docstring of ``guess`` for further information.
```


### `guess_qrec`

```
Shortcut for ``guess`` applied with an Ore algebra of `q`-recurrence operators in `Q` over `K[qn]`
where `K` is the parent of `q`.

See the docstring of ``guess`` for further information.
```


### `guess`

```
Searches for an element of the algebra which annihilates the given data.

INPUT:

- ``data`` -- a list of elements of the algebra's base ring's base ring `K` (or at least
  of objects which can be casted into this ring). If ``data`` is a string, it is assumed
  to be the name of a text file which contains the terms, one per line, encoded in a way
  that can be interpreted by the element constructor of `K`.
- ``algebra`` -- a univariate Ore algebra over a univariate polynomial ring whose
  generator is the standard derivation, the standard shift, the forward difference,
  a q-shift, or a commutative variable.

Optional arguments:

- ``cut`` -- if `N` is the minimum number of terms needed for some particular
  choice of order and degree, and if ``len(data)`` is more than ``N+cut``,
  use ``data[:N+cut]`` instead of ``data``. This must be a nonnegative integer
  or ``None``. Default: ``None``.
- ``ensure`` -- if `N` is the minimum number of terms needed for some particular
  choice of order and degree, and if ``len(data)`` is less than ``N+ensure``,
  raise an error. This must be a nonnegative integer. Default: 0.
- ``ncpus`` -- number of processors to be used. Default: 1.
- ``order`` -- bounds the order of the operators being searched for.
  Default: infinity.
- ``min_order`` -- smallest order to be considered in the search. The output
  may nevertheless have lower order than this bound. Default: 1
- ``degree`` -- bounds the degree of the operators being searched for.
  The method may decide to overrule this setting if it thinks this may speed up
  the calculation. Default: infinity.
- ``min_degree`` -- smallest degree to be considered in the search. The output
  may nevertheless have lower degree than this bound. Default: 0
- ``path`` -- a list of pairs `(r, d)` specifying which orders and degrees
  the method should attempt. If this value is equal to ``None`` (default), a
  path is chosen which examines all the `(r, d)` which can be tested with the
  given amount of data.
- ``solver`` -- function to be used for computing the right kernel of a matrix
  with elements in `K`.
- ``infolevel`` -- an integer specifying the level of details of progress
  reports during the calculation.
- ``method`` -- either "linalg" (for linear algebra) or "hp" (for Hermite-Pade) or "automatic"
  (for the default choice), or a callable with the specification of a raw guesser.

OUTPUT:

- An element of ``algebra`` which annihilates the given ``data``.

An error is raised if no such element is found.

.. NOTE::

    - This method is designed to find equations for D-finite objects. It
      may exhibit strange behaviour for objects which are holonomic but not
      D-finite.
    - When the generator of the algebra is a commutative variable, the
      method searches for algebraic equations.

EXAMPLES::

  sage: from ore_algebra import *
  sage: rec = guess([(2*i+1)^15 * (1 + 2^i + 3^i)^2 for i in range(1000)], OreAlgebra(ZZ['n'], 'Sn')) # long time (2.9 s)
  sage: rec.order(), rec.degree() # long time
  (6, 90)
  sage: R.<t> = QQ['t']
  sage: rec = guess([1/(i+t) + t^i for i in range(100)], OreAlgebra(R['n'], 'Sn'))
  sage: rec
  ((-t + 1)*n^2 + (-2*t^2 - t + 2)*n - t^3 - 2*t^2)*Sn^2 + ((t^2 - 1)*n^2 + (2*t^3 + 3*t^2 - 2*t - 1)*n + t^4 + 3*t^3 + t^2 - t)*Sn + (-t^2 + t)*n^2 + (-2*t^3 + t)*n - t^4 - t^3 + t^2

  sage: R.<C> = OreAlgebra(ZZ['x'])
  sage: cat = [binomial(2*n,n) // (n+1) for n in range(10)]
  sage: guess(cat, R)
  -x*C^2 + C - 1
```


### `guess_raw`

```
Guesses recurrence or differential equations for a given sample of terms.

INPUT:

- ``data`` -- list of terms
- ``A`` -- an Ore algebra of recurrence operators, differential operators,
  or q-differential operators.
- ``order`` -- maximum order of the sought operators
- ``degree`` -- maximum degree of the sought operators
- ``lift`` (optional) -- a function to be applied to the terms in ``data``
  prior to computation
- ``solver`` (optional) -- a function to be used to compute the nullspace
  of a matrix with entries in the base ring of the base ring of ``A``
- ``cut`` (optional) -- if `N` is the minimum number of terms needed for
  the the specified order and degree and ``len(data)`` is more than ``N+cut``,
  use ``data[:N+cut]`` instead of ``data``. This must be a nonnegative integer
  or ``None``.
- ``ensure`` (optional) -- if `N` is the minimum number of terms needed
  for the specified order and degree and ``len(data)`` is less than ``N+ensure``,
  raise an error. This must be a nonnegative integer.
- ``infolevel`` (optional) -- an integer indicating the desired amount of
  progress report to be printed during the calculation. Default: 0 (no output).

OUTPUT:

A basis of the ``K``-vector space of all the operators `L` in ``A`` of order
at most ``order`` and degree at most ``degree`` such that `L` applied to
``data`` gives an array of zeros. (resp. `L` applied to the truncated power
series with ``data`` as terms gives the zero power series)

An error is raised in the following situations:

* the algebra ``A`` has more than one generator, or its unique generator
  is neither a standard shift nor a q-shift nor a standard derivation.
* ``data`` contains some item which does not belong to ``K``, even after
  application of ``lift``
* if the condition on ``ensure`` is violated.
* if the linear system constructed by the method turns out to be
  underdetermined for some other reason, e.g., because too many linear
  constraints happen to be trivial.

ALGORITHM:

Ansatz and linear algebra.

.. NOTE::

  This is a low-level method. Don't call it directly unless you know what you
  are doing. In usual applications, the right method to call is ``guess``.

EXAMPLES::

  sage: from ore_algebra import *
  sage: K = GF(1091); R.<n> = K['n']; A = OreAlgebra(R, 'Sn')
  sage: data = [(5*n+3)/(3*n+4)*fibonacci(n)^3 for n in range(200)]
  sage: guess_raw(data, A, order=5, degree=3, lift=K)
  [(n^3 + 546*n^2 + 588*n + 786)*Sn^5 + (356*n^3 + 717*n^2 + 381*n + 449)*Sn^4 + (8*n^3 + 569*n^2 + 360*n + 214)*Sn^3 + (31*n^3 + 600*n^2 + 784*n + 287)*Sn^2 + (1078*n^3 + 1065*n^2 + 383*n + 466)*Sn + 359*n^3 + 173*n^2 + 503, (n^3 + 1013*n^2 + 593*n + 754)*Sn^5 + (797*n^3 + 56*n^2 + 7*n + 999)*Sn^4 + (867*n^3 + 1002*n^2 + 655*n + 506)*Sn^3 + (658*n^3 + 834*n^2 + 1036*n + 899)*Sn^2 + (219*n^3 + 479*n^2 + 476*n + 800)*Sn + 800*n^3 + 913*n^2 + 280*n]
```


### `guess_hp`

```
Guesses differential equations or algebraic equations for a given sample of terms.

INPUT:

- ``data`` -- list of terms
- ``A`` -- an Ore algebra of differential operators or ordinary polynomials.
- ``order`` -- maximum order of the sought operators
- ``degree`` -- maximum degree of the sought operators
- ``lift`` (optional) -- a function to be applied to the terms in ``data``
  prior to computation
- ``cut`` (optional) -- if `N` is the minimum number of terms needed for
  the the specified order and degree and ``len(data)`` is more than ``N+cut``,
  use ``data[:N+cut]`` instead of ``data``. This must be a nonnegative integer
  or ``None``.
- ``ensure`` (optional) -- if `N` is the minimum number of terms needed
  for the specified order and degree and ``len(data)`` is less than ``N+ensure``,
  raise an error. This must be a nonnegative integer.
- ``infolevel`` (optional) -- an integer indicating the desired amount of
  progress report to be printed during the calculation. Default: 0 (no output).

OUTPUT:

A basis of the ``K``-vector space of all the operators `L` in ``A`` of order
at most ``order`` and degree at most ``degree`` such that `L` applied to
the truncated power series with ``data`` as terms gives the zero power series.

An error is raised in the following situations:

* the algebra ``A`` has more than one generator, or its unique generator
  is neither a standard derivation nor a commutative variable.
* ``data`` contains some item which does not belong to ``K``, even after
  application of ``lift``
* if the condition on ``ensure`` is violated.

ALGORITHM:

Hermite-Pade approximation.

.. NOTE::

  This is a low-level method. Don't call it directly unless you know what you
  are doing. In usual applications, the right method to call is ``guess``.

EXAMPLES::

  sage: from ore_algebra import *
  sage: from ore_algebra.guessing import guess_hp
  sage: K = GF(1091); R.<x> = K['x'];
  sage: data = [binomial(2*n, n)*fibonacci(n)^3 for n in range(2000)]
  sage: guess_hp(data, OreAlgebra(R, 'Dx'), order=4, degree=4, lift=K)
  [(x^4 + 819*x^3 + 136*x^2 + 17*x + 635)*Dx^4 + (14*x^3 + 417*x^2 + 952*x + 605)*Dx^3 + (598*x^2 + 497*x + 99)*Dx^2 + (598*x + 794)*Dx + 893]
  sage: len(guess_hp(data, OreAlgebra(R, 'C'), order=16, degree=64, lift=K))
  1
```


### `guess_mult`

```
Searches for elements of the algebra which annihilates the given data.

INPUT:

- ``data`` -- a nested list of elements of the algebra's base ring's base ring `K` (or at least
  of objects which can be casted into this ring).
  The depth of the nesting must match the number of generators of the algebra.
- ``algebra`` -- an Ore algebra over a polynomial ring all of whose generators are
  the standard derivation, the standard shift, or a q-shift.

Optional arguments:

- ``cut`` -- if `N` is the minimum number of terms needed for some particular
  choice of order and degree, and if ``len(data)`` is more than ``N+cut``,
  use ``data[:N+cut]`` instead of ``data``. This must be a nonnegative integer
  or ``None``. Default: 100.
- ``ensure`` -- if `N` is the minimum number of terms needed for some particular
  choice of order and degree, and if ``len(data)`` is less than ``N+ensure``,
  raise an error. This must be a nonnegative integer. Default: 0.
- ``order`` -- maximum degree of the algebra generators in the sought operators.
  Alternatively: a list or tuple specifying individual degree bounds for each
  generator of the algebra. Default: 2
- ``degree`` -- maximum total degree of the polynomial coefficients in the sought
  operators. Default: 3
- ``point_filter`` -- a callable such that index tuples of data array for which
  the callable returns 'False' will not be used. Default: None (everything allowed).
- ``term_filter`` -- a callable such that operators containing power products of
  the algebra generators for which the callable returns 'False' are excluded.
  Default: None (everything allowed).
- ``solver`` -- function to be used for computing the right kernel of a matrix
  with elements in `K`.
- ``infolevel`` -- an integer specifying the level of details of progress
  reports during the calculation.

OUTPUT:

- The left ideal of ``algebra`` generated by all the operators of the specified order and degree
  that annihilate the given ``data``. It may be the zero ideal.

.. NOTE::

    This method is designed to find equations for D-finite objects. It may
    exhibit strange behaviour for objects which are holonomic but not
    D-finite.

EXAMPLES::

  sage: from ore_algebra import *
  sage: from ore_algebra.guessing import guess_mult
  sage: data = [[binomial(n,k) for n in range(10)] for k in range(10)]
  sage: guess_mult(data, OreAlgebra(ZZ['n','k'], 'Sn', 'Sk'), order=1, degree=0)
  Left Ideal (Sn*Sk - Sn - 1) of Multivariate Ore algebra in Sn, Sk over Fraction Field of Multivariate Polynomial Ring in n, k over Integer Ring
  sage: guess_mult(data, OreAlgebra(ZZ['x','y'], 'Dx', 'Dy'), order=1, degree=1)
  Left Ideal ((x + 1)*Dx + (-y)*Dy) of Multivariate Ore algebra in Dx, Dy over Fraction Field of Multivariate Polynomial Ring in x, y over Integer Ring
  sage: guess_mult(data, OreAlgebra(ZZ['n','y'], 'Sn', 'Dy'), order=1, degree=1)
  Left Ideal ((-y + 1)*Sn*Dy - Sn + (-y)*Dy - 1, (-n - 1)*Sn + y*Dy - n, (-y + 1)*Sn - y) of Multivariate Ore algebra in Sn, Dy over Fraction Field of Multivariate Polynomial Ring in n, y over Integer Ring
  sage: guess_mult(data, OreAlgebra(ZZ['x','k'], 'Dx', 'Sk'), order=1, degree=1)
  Left Ideal (Dx*Sk + (-x - 1)*Dx - 1, x*Dx*Sk + (x + 1)*Dx + (-k)*Sk - x, (x + 1)*Dx - k, (x + 1)*Dx*Sk + (-k - 1)*Sk) of Multivariate Ore algebra in Dx, Sk over Fraction Field of Multivariate Polynomial Ring in x, k over Integer Ring
```


### `guess_mult_raw`

```
Low-level multivariate guessing function. Do not call this method unless you know what you are doing.
In most situations, you will want to call the function `guess` instead.

INPUT:

- `data` -- a nested list of elements of C
- `terms` -- a list of pairs of tuples (u, v) specifying exponent vectors u, v representing terms x^u D^v
- `points` -- a list of tuples specifying indices of the data array
- `power` -- a list of functions f mapping triples (n, u, v) of nonnegative integers to elements of C
- `A` -- a list of functions mapping triples (n, u, v) to integers
- `B` -- a list of functions mapping triples (n, u, v) to integers

OUTPUT:

A list of vectors generating the space of all vectors in C^len(terms) for which
all(sum(prod(f[i][A[i][n[i],u[i],v[i]]]*a[B[i][n[i],u[i],v[i]]] for i in range(len(A)))
for u,v in terms) == 0 for n in points)

SIDE EFFECT:

Elements of the list `points` which lead to a zero equation will be discarded.
```

### `UnivariateOreOperatorOverUnivariateRing.polynomial_solutions`

```
Computes the polynomial solutions of this operator.

INPUT:

- ``rhs`` (optional) -- a list of base ring elements
- ``degree`` (optional) -- bound on the degree of interest.
- ``solver`` (optional) -- a callable for computing the right kernel
  of a matrix over the base ring's base ring.

OUTPUT:

A list of tuples `(p, c_0,...,c_r)` such that `self(p) == c_0*rhs[0] + ... + c_r*rhs[r]`,
where `p` is a polynomial and `c_0,...,c_r` are constants.

.. NOTE::

    - Even if no ``rhs`` is given, the output will be a list of tuples ``[(p1,), (p2,),...]``
      and not just a list of plain polynomials.
    - If no ``degree`` is given, a basis of all the polynomial solutions is returned.
      This feature may not be implemented for all algebras.

EXAMPLES::

    sage: from ore_algebra import *
    sage: R.<n> = ZZ['n']; A.<Sn> = OreAlgebra(R, 'Sn')
    sage: L = 2*Sn^2 + 3*(n-7)*Sn + 4
    sage: L.polynomial_solutions((n^2+4*n-8, 4*n^2-5*n+3))
    [(-70*n + 231, 242, -113)]
    sage: L(-70*n + 231)
    -210*n^2 + 1533*n - 2275
    sage: 242*(n^2+4*n-8) - 113*(4*n^2-5*n+3)
    -210*n^2 + 1533*n - 2275

    sage: R.<x> = ZZ['x']; A.<Dx> = OreAlgebra(R, 'Dx')
    sage: L = (x*Dx - 19).lclm( x*Dx - 4 )
    sage: L.polynomial_solutions()
    [(x^4,), (x^19,)]
```


### `UnivariateOreOperatorOverUnivariateRing.rational_solutions`

```
Computes the rational solutions of this operator.

INPUT:

- ``rhs`` (optional) -- a list of base ring elements
- ``denominator`` (optional) -- bound on the degree of interest.
- ``degree`` (optional) -- bound on the degree of interest.
- ``solver`` (optional) -- a callable for computing the right kernel
  of a matrix over the base ring's base ring.

OUTPUT:

A list of tuples `(r, c_0,...,c_r)` such that `self(r) == c_0*rhs[0] + ... + c_r*rhs[r]`,
where `r` is a rational function and `c_0,...,c_r` are constants.

.. NOTE::

    - Even if no ``rhs`` is given, the output will be a list of tuples ``[(p1,), (p2,),...]``
      and not just a list of plain rational functions.
    - If no ``denominator`` is given, a basis of all the rational solutions is returned.
      This feature may not be implemented for all algebras.
    - If no ``degree`` is given, a basis of all the polynomial solutions is returned.
      This feature may not be implemented for all algebras.

EXAMPLES::

    sage: from ore_algebra import *
    sage: R.<x> = ZZ['x']; A.<Dx> = OreAlgebra(R, 'Dx')
    sage: L = ((x+3)*Dx + 2).lclm(x*Dx + 3).symmetric_product((x+4)*Dx-2)
    sage: L.rational_solutions()
    [((-x^2 - 8*x - 16)/x^3,),
     ((-x^5 + 96*x^3 + 584*x^2 + 1344*x + 1152)/(x^5 + 6*x^4 + 9*x^3),)]
    sage: L.rational_solutions((1, x))
    [((x^2 + 8*x + 16)/(x^2 + 6*x + 9), 0, 0),
     ((x^5 + 7*x^4 + 2*x^3 - 73*x^2 - 168*x - 144)/(x^5 + 6*x^4 + 9*x^3), 0, 0),
     ((-2*x - 7)/(x^2 + 6*x + 9), 288, 42)]
    sage: L(_[0][0]) == _[0][1] + _[0][2]*x
    True

    sage: (x*(x*Dx-5)).rational_solutions([1])
    [(-x^5, 0), (1/x, -6)]

    sage: R.<n> = ZZ['n']; A.<Sn> = OreAlgebra(R, 'Sn');
    sage: L = ((n+3)*Sn - n).lclm((2*n+5)*Sn - (2*n+1))
    sage: L.rational_solutions()
    [(-1/(n^3 + 3*n^2 + 2*n),),
     ((-n^3 + n^2 + 6*n + 3)/(4*n^5 + 20*n^4 + 35*n^3 + 25*n^2 + 6*n),)]

    sage: L = (2*n^2 - n - 2)*Sn^2 + (-n^2 - n - 1)*Sn + n^2 - 14
    sage: y = (-n + 1)/(n^2 + 2*n - 2)
    sage: L.rational_solutions((L(y),))
    [((n - 1)/(n^2 + 2*n - 2), -1)]
```


## Selected operator methods


### `UnivariateDifferentialOperatorOverUnivariateRing.to_S`  (differential operators (D))

```
Return a recurrence operator annihilating the coefficient sequence of
every power series (about the origin) annihilated by ``self``.

INPUT:

- ``alg`` -- the Ore algebra in which the output should be expressed.
  The algebra must satisfy ``alg.base_ring().base_ring() == self.base_ring().base_ring()``
  and ``alg.is_S()`` is not ``False``.
  Instead of an algebra object, also a string can be passed as argument.
  This amounts to specifying an Ore algebra over ``self.base_ring()`` with
  the standard shift with respect to ``self.base_ring().gen()``.

EXAMPLES::

    sage: from ore_algebra import *
    sage: R.<x> = ZZ['x']
    sage: A.<Dx> = OreAlgebra(R, 'Dx')
    sage: R2.<n> = ZZ['n']
    sage: A2.<Sn> = OreAlgebra(R2, 'Sn')
    sage: (Dx - 1).to_S(A2)
    (n + 1)*Sn - 1
    sage: ((1+x)*Dx^2 + Dx).to_S(A2)
    (n^2 + n)*Sn + n^2
    sage: ((x^3+x^2-x)*Dx + (x^2+1)).to_S(A2)
    (-n - 1)*Sn^2 + (n + 1)*Sn + n + 1
    sage: ((x+1)*Dx^3 + Dx^2).to_S(A2)
    (n^3 - n)*Sn + n^3 - 2*n^2 + n
```


### `UnivariateDifferentialOperatorOverUnivariateRing.to_T`  (differential operators (D))

```
Rewrite ``self`` in terms of the eulerian derivation `x*d/dx`.

If the base ring of the target algebra is not a field, the
operator returned by the method may not correspond exactly to
``self``, but only to a suitable left-multiple by a term `x^k`.

INPUT:

- ``alg`` -- the Ore algebra in which the output should be expressed.
  The algebra must satisfy ``alg.base_ring().base_ring() == self.base_ring().base_ring()``
  and ``alg.is_T()`` is not ``False``.
  Instead of an algebra object, also a string can be passed as argument.
  This amounts to specifying an Ore algebra over ``self.base_ring()`` with
  an euler derivation with respect to ``self.base_ring().gen()``.

EXAMPLES::

    sage: from ore_algebra import *
    sage: R.<x> = ZZ['x']
    sage: R2.<y> = ZZ['y']
    sage: A.<Dx> = OreAlgebra(R, 'Dx')
    sage: (Dx^4).to_T(OreAlgebra(R2, 'Ty'))
    Ty^4 - 6*Ty^3 + 11*Ty^2 - 6*Ty
    sage: (Dx^4).to_T('Tx').to_D(A)
    x^4*Dx^4
    sage: _.to_T('Tx')
    Tx^4 - 6*Tx^3 + 11*Tx^2 - 6*Tx
```


### `UnivariateDifferentialOperatorOverUnivariateRing.annihilator_of_integral`  (differential operators (D))

```
Return an operator `L` which annihilates all the indefinite integrals `\int f`
where `f` runs through the functions annihilated by ``self``.

The output operator is not necessarily of smallest possible order.

EXAMPLES::

    sage: from ore_algebra import *
    sage: R.<x> = ZZ['x']
    sage: A.<Dx> = OreAlgebra(R, 'Dx')
    sage: ((x-1)*Dx - 2*x).annihilator_of_integral()
    (x - 1)*Dx^2 - 2*x*Dx
    sage: _.annihilator_of_associate(Dx)
    (x - 1)*Dx - 2*x
```


### `UnivariateDifferentialOperatorOverUnivariateRing.annihilator_of_composition`  (differential operators (D))

```
Return an operator `L` which annihilates all the functions `f(a(x))` where
`f` runs through the functions annihilated by ``self``, and, optionally,
a map from the quotient by ``self`` to the quotient by `L` commuting
with the composition by `a`.

The output operator `L` is not necessarily of smallest possible order.

INPUT:

- ``a`` -- either an element of the base ring of the parent of ``self``,
  or an element of an algebraic extension of this ring.
- ``solver`` (optional) -- a callable object which applied to a matrix
  with polynomial entries returns its kernel.
- ``with_transform`` (optional) -- if `True`, also return a
  transformation map between the quotients

OUTPUT:

- ``L`` -- an Ore operator such that for all ``f`` annihilated by
  ``self``, ``L`` annihilates ``f \circ a``.
- ``conv`` -- a function which takes as input an Ore operator ``P`` and
  returns an Ore operator ``Q`` such that for all functions ``f``
  annihilated by ``self``, ``P(f)(a(x)) = Q(f \circ a)(x)``.

EXAMPLES::

    sage: from ore_algebra import *
    sage: R.<x> = ZZ['x']
    sage: K.<y> = R.fraction_field()['y']
    sage: K.<y> = R.fraction_field().extension(y^3 - x^2*(x+1))
    sage: A.<Dx> = OreAlgebra(R, 'Dx')
    sage: (x*Dx-1).annihilator_of_composition(y) # ann for x^(2/3)*(x+1)^(1/3)
    (3*x^2 + 3*x)*Dx - 3*x - 2
    sage: (x*Dx-1).annihilator_of_composition(y + 2*x) # ann for 2*x + x^(2/3)*(x+1)^(1/3)
    (3*x^3 + 3*x^2)*Dx^2 - 2*x*Dx + 2
    sage: (Dx - 1).annihilator_of_composition(y) # ann for exp(x^(2/3)*(x+1)^(1/3))
    (-243*x^6 - 810*x^5 - 999*x^4 - 540*x^3 - 108*x^2)*Dx^3 + (-162*x^3 - 270*x^2 - 108*x)*Dx^2 + (162*x^2 + 180*x + 12)*Dx + 243*x^6 + 810*x^5 + 1080*x^4 + 720*x^3 + 240*x^2 + 32*x

If composing with a rational function, one can also compute the
transformation map between the quotients.::

    sage: L = x*Dx^2 + 1
    sage: LL, conv = L.annihilator_of_composition(x+1, with_transform=True)
    sage: print(LL)
    (x + 1)*Dx^2 + 1
    sage: print(conv(Dx))
    Dx
    sage: print(conv(x*Dx))
    (x + 1)*Dx
    sage: print(conv(L))
    0
    sage: LL, conv = L.annihilator_of_composition(1/x, with_transform=True)
    sage: print(LL)
    -x^3*Dx^2 - 2*x^2*Dx - 1
    sage: print(conv(Dx))
    -x^2*Dx
    sage: print(conv(x*Dx))
    -x*Dx
    sage: print(conv(conv(x*Dx))) # identity since 1/1/x = x
    x*Dx
    sage: LL, conv = L.annihilator_of_composition(1+x^2, with_transform=True)
    sage: print(LL)
    (-x^3 - x)*Dx^2 + (x^2 + 1)*Dx - 4*x^3
    sage: print(conv(Dx))
    1/(2*x)*Dx
    sage: print(conv(x*Dx))
    ((x^2 + 1)/(2*x))*Dx
```


### `UnivariateDifferentialOperatorOverUnivariateRing.power_series_solutions`  (differential operators (D))

```
Compute the first few terms of the power series solutions of this operator.

The method raises an error if Sage does not know how to factor
univariate polynomials over the base ring's base ring.

The base ring has to have characteristic zero.

INPUT:

- ``n`` -- minimum number of terms to be computed

OUTPUT:

A list of power series of the form `x^\alpha + ...` with pairwise distinct
exponents `\alpha` and coefficients in the base ring's base ring's fraction field.
All expansions are computed up to order `k` where `k` is obtained by adding the
maximal `\alpha` to the maximum of `n` and the order of ``self``.

EXAMPLES::

    sage: from ore_algebra import *
    sage: R.<x> = ZZ['x']
    sage: A.<Dx> = OreAlgebra(R, 'Dx')
    sage: ((1-x)*Dx - 1).power_series_solutions(10) # geometric series
    [1 + x + x^2 + x^3 + x^4 + x^5 + x^6 + x^7 + x^8 + O(x^9)]
    sage: (Dx - 1).power_series_solutions(5) # exp(x)
    [1 + x + 1/2*x^2 + 1/6*x^3 + O(x^4)]
    sage: (Dx^2 - Dx + x).power_series_solutions(5) # a 2nd order equation
    [x + 1/2*x^2 + 1/6*x^3 - 1/24*x^4 + O(x^5), 1 - 1/6*x^3 - 1/24*x^4 + O(x^5)]
    sage: (2*x*Dx - 1).power_series_solutions(5) # sqrt(x) is not a power series
    []
```


### `UnivariateDifferentialOperatorOverUnivariateRing.generalized_series_solutions`  (differential operators (D))

```
Return the generalized series solutions of this operator.

These are solutions of the form

  `\exp(\int_0^x \frac{p(t^{-1/s})}t dt)*q(x^{1/s},\log(x))`

where

* `s` is a positive integer (the object's "ramification")
* `p` is in `K[x]` (the object's "exponential part")
* `q` is in `K[[x]][y]` with `x\nmid q` unless `q` is zero (the object's "tail")
* `K` is some algebraic extension of the base ring's base ring.

An operator of order `r` has exactly `r` linearly independent solutions of this form.
This method computes them all, unless the flags specified in the arguments rule out some
of them.

At present, the method only works for operators where the base ring's base ring is either
QQ or a number field (i.e., no finite fields, no formal parameters).

INPUT:

- ``n`` (default: 5) -- minimum number of terms in the series expansions to be computed
  in addition to those needed to separate all solutions from each other.
- ``base_extend`` (default: ``True``) -- whether or not the coefficients of the solutions may
  belong to an algebraic extension of the base ring's base ring.
- ``ramification`` (default: ``True``) -- whether or not the exponential parts of the solutions
  may involve fractional exponents.
- ``exp`` (default: ``True``) -- set this to ``False`` if you only want solutions that have no
  exponential part (viz `\deg(p)\leq0`). If set to a positive rational number `\alpha`,
  the method returns all those solutions whose exponential part involves only terms `x^{-i/r}`
  with `i/r<\alpha`.

OUTPUT:

- a list of ``ContinuousGeneralizedSeries`` objects forming a fundamental system for this operator.

.. NOTE::

  - Different solutions may require different algebraic extensions. Thus in the list returned
    by this method, the coefficient fields of different series typically do not coincide.
  - If a solution involves an algebraic extension of the coefficient field, then all its
    conjugates are solutions, too. But only one representative is listed in the output.

ALGORITHM:

- Ince, Ordinary Differential Equations, Chapters 16 and 17
- Kauers/Paule, The Concrete Tetrahedron, Section 7.3

EXAMPLES::

    sage: from ore_algebra import *
    sage: R.<x> = QQ['x']; A.<Dx> = OreAlgebra(R, 'Dx')
    sage: L = (6+6*x-3*x^2) - (10*x-3*x^2-3*x^3)*Dx + (4*x^2-6*x^3+2*x^4)*Dx^2
    sage: L.generalized_series_solutions()
    [x^3*(1 + 3/2*x + 7/4*x^2 + 15/8*x^3 + 31/16*x^4 + O(x^5)), x^(1/2)*(1 + 3/2*x + 7/4*x^2 + 15/8*x^3 + 31/16*x^4 + O(x^5))]
    sage: list(map(L, _))
    [0, 0]

    sage: L = (1-24*x+96*x^2) + (15*x-117*x^2+306*x^3)*Dx + (9*x^2-54*x^3)*Dx^2
    sage: L.generalized_series_solutions(3)
    [x^(-1/3)*(1 + x + 8/3*x^2 + O(x^3)), x^(-1/3)*((1 + x + 8/3*x^2 + O(x^3))*log(x) + x - 59/12*x^2 + O(x^3))]
    sage: list(map(L, _))
    [0, 0]

    sage: L = 216*(1+x+x^3) + x^3*(36-48*x^2+41*x^4)*Dx - x^7*(6+6*x-x^2+4*x^3)*Dx^2
    sage: L.generalized_series_solutions(3)
    [exp(3*x^(-2))*x^(-2)*(1 + 91/12*x^2 + O(x^3)), exp(-2*x^(-3) + x^(-1))*x^2*(1 + 41/3*x + 2849/36*x^2 + O(x^3))]
    sage: list(map(L, _))
    [0, 0]

    sage: L = 9 - 49*x - 2*x^2 + 6*x^2*(7 + 5*x)*Dx + 36*(-1 + x)*x^3*Dx^2
    sage: L.generalized_series_solutions()
    [exp(x^(-1/2))*x^(4/3)*(1 + x^(2/2) + x^(4/2)), exp(-x^(-1/2))*x^(4/3)*(1 + x^(2/2) + x^(4/2))]
    sage: L.generalized_series_solutions(ramification=False)
    []

    sage: L = 2*x^3*Dx^2 + 3*x^2*Dx-1
    sage: L.generalized_series_solutions()
    [exp(a_0*x^(-1/2))]
    sage: _[0].base_ring()
    Number Field in a_0 with defining polynomial x^2 - 2
```


### `UnivariateDifferentialOperatorOverUnivariateRing.numerical_solution`  (differential operators (D))

```
Evaluate an analytic solution of this operator at a point of its Riemann
surface.

INPUT:

- ``ini`` (iterable) - initial values, in number equal to the order `r`
  of the operator
- ``path`` - a path on the complex plane, specified as a list of
  vertices `z_0, \dots, z_n`
- ``eps`` (floating-point number or ball, default 1e-16) - approximate
  target accuracy
- ``post_transform`` (default: identity) - differential operator to be
  applied to the solutions, see examples below
- see :class:`ore_algebra.analytic.context.Context` for advanced
  options

OUTPUT:

A real or complex ball *enclosing* the value at `z_n` of the solution `y`
defined in the neighborhood of `z_0` by the initial values ``ini`` and
extended by analytic continuation along ``path``.

When `z_0` is an ordinary point, the initial values are defined as the
first `r` coefficients of the power series expansion at `z_0` of the
desired solution `f`. In other words, ``ini`` must be equal to

.. math:: [f(z_0), f'(z_0), f''(z_0)/2, \dots, f^{(r-1)}(z_0)/(r-1)!].

Generalized initial conditions at regular singular points are also
supported. If `z_0` is a regular point, the entries of ``ini`` are
interpreted as the coefficients of the monomials `(z-z_0)^n
\log(z-z_0)^k/k!` returned by :meth:`local_basis_monomials` in the
logarithmic series expansion of `f` at `z_0`. This definition reduces
to the previous one when `z_0` is an ordinary point.

The accuracy parameter ``eps`` is used as an indication of the
*absolute* error the code should aim for. The diameter of the result
will typically be of the order of magnitude of ``eps``, but this is not
guaranteed to be the case. (It is a bug, however, if the returned ball
does not contain the exact result.)

See :mod:`ore_algebra.analytic` for more information, and
:mod:`ore_algebra.examples` for additional examples.

.. SEEALSO:: :meth:`numerical_transition_matrix`

EXAMPLES:

First a very simple example::

    sage: from ore_algebra import DifferentialOperators
    sage: Dops, x, Dx = DifferentialOperators()
    sage: (Dx - 1).numerical_solution(ini=[1], path=[0, 1], eps=1e-50)
    [2.7182818284590452353602874713526624977572470936999...]

Evaluation points can be complex and can depend on symbolic constants::

    sage: (Dx - 1).numerical_solution([1], [0, i + pi])
    [12.5029695888765...] + [19.4722214188416...]*I

They can even be real or complex balls. In this case, the result
contains the image of the ball::

    sage: (Dx - 1).numerical_solution([1], [0, CBF(1+i).add_error(0.01)])
    [1.5 +/- 0.0693] + [2.3 +/- 0.0506]*I

Here, we use a more complicated analytic continuation path in order to
evaluate the branch of the complex arctangent function obtained by
turning around its singularity at `i` once::

    sage: dop = (x^2 + 1)*Dx^2 + 2*x*Dx
    sage: dop.numerical_solution([0, 1], [0, i+1, 2*i, i-1, 0])
    [3.14159265358979...] + [+/- ...]*I

In some cases, this method is also able to compute limits of solutions
at regular singular points. This only works when all solutions of the
differential equation tend to finite values at the evaluation point::

    sage: dop = (x - 1)^2*Dx^3 + Dx + 1
    sage: dop.local_basis_monomials(1)
    [1,
    (x - 1)^(1.500000000000000? - 0.866025403784439?*I),
    (x - 1)^(1.500000000000000? + 0.866025403784439?*I)]
    sage: dop.numerical_solution(ini=[1, 0, 0], path=[0, 1])
    [0.6898729110219401...] + [+/- ...]*I

    sage: dop = -(x+1)*(x-1)^3*Dx^2 + (x+3)*(x-1)^2*Dx - (x+3)*(x-1)
    sage: dop.local_basis_monomials(1)
    [x - 1, (x - 1)^2]
    sage: dop.numerical_solution([1,0], [0,1])
    0

    sage: (Dx*x*Dx).numerical_solution(ini=[1,0],path=[1,0])
    Traceback (most recent call last):
    ...
    ValueError: solution may not have a finite limit at evaluation
    point 0 (try using numerical_transition_matrix())

To obtain the values of the solution at several points in a single run,
enclose the corresponding points of the path in length-one lists. The
output then changes to a list of (point, solution value) pairs::

    sage: (Dx - 1).numerical_solution([1], [[i/3] for i in range(4)])
    [(0, 1.00...), (1/3, [1.39...]), (2/3, [1.94...]), (1, [2.71...])]

    sage: (Dx - 1).numerical_solution([1], [0, [1]])
    [(1, [2.71828182845904...])]

The ``post_transform`` parameter can be used to compute derivatives or
linear combinations of derivatives of the solution. Here, we use this
feature to evaluate the tenth derivative of the Airy `Ai` function::

    sage: ini = [1/(3^(2/3)*gamma(2/3)), -1/(3^(1/3)*gamma(1/3))]
    sage: (Dx^2-x).numerical_solution(ini, [0,2], post_transform=Dx^10)
    [2.34553207877...]
    sage: airy_ai(10, 2.)
    2.345532078777...

A similar, slightly more complicated example::

    sage: (Dx^2 - x).numerical_solution(ini, [0, 2],
    ....:                               post_transform=1/x + x*Dx)
    [-0.08871870365567...]
    sage: t = SR.var('t')
    sage: (airy_ai(t)/t + t*airy_ai_prime(t))(t=2.)
    -0.08871870365567...

Some no
... [truncated]
```


### `UnivariateDifferentialOperatorOverUnivariateRing.numerical_transition_matrix`  (differential operators (D))

```
Compute a transition matrix along a path drawn in the complex plane.

INPUT:

- ``path`` - a path on the complex plane, specified as a list of
  vertices `z_0, \dots, z_n`
- ``eps`` (floating-point number or ball) - target accuracy
- see :class:`ore_algebra.analytic.context.Context` for advanced
  options

OUTPUT:

When ``self`` is an operator of order `r`, this method returns an `r×r`
matrix of real or complex balls. The returned matrix maps a vector of
“initial values at `z_0`” (i.e., the coefficients of the decomposition
of a solution in a certain canonical local basis at `z_0`) to “initial
values at `z_n`” that define the same solution, extended by analytic
continuation along the path ``path``.

The “initial values” are the coefficients of the monomials returned by
:meth:`local_basis_monomials` in the local logarithmic power series
expansions of the solution at the corresponding point. When `z_i` is an
ordinary point, the corresponding vector of initial values is simply

.. math:: [f(z_i), f'(z_i), f''(z_i)/2, \dots, f^{(r-1)}(z_i)/(r-1)!].

The accuracy parameter ``eps`` is used as an indication of the
*absolute* error that the code should aim for. The diameter of each
entry of the result will typically be of the order of magnitude of
``eps``, but this is not guaranteed to be the case. (It is a bug,
however, if the returned ball does not contain the exact result.)

See :mod:`ore_algebra.analytic` for more information, and
:mod:`ore_algebra.examples` for additional examples.

.. SEEALSO:: :meth:`numerical_solution`

EXAMPLES:

We can compute `\exp(1)` as the only entry of the transition matrix from
`0` to `1` for the differential equation `y' = y`::

    sage: from ore_algebra import DifferentialOperators
    sage: Dops, x, Dx = DifferentialOperators()
    sage: (Dx - 1).numerical_transition_matrix([0, 1])
    [[2.7182818284590452 +/- 3.54e-17]]

Now consider a second-order operator that annihilates `\arctan(x)` and the
constants. A basis of solutions is formed of the constant `1`, of the
form `1 + O(x^2)` as `x \to 0`, and the arctangent function, of the form
`x + O(x^2)`. Accordingly, the entries of the transition matrix from the
origin to `1 + i` are the values of these two functions and their first
derivatives::

    sage: dop = (x^2 + 1)*Dx^2 + 2*x*Dx
    sage: dop.numerical_transition_matrix([0, 1+i], 1e-10)
    [ [1.00...] + [+/- ...]*I  [1.017221967...] + [0.4023594781...]*I]
    [ [+/- ...] + [+/- ...]*I  [0.200000000...] + [-0.400000000...]*I]

By making loops around singular points, we can compute local monodromy
matrices::

    sage: dop.numerical_transition_matrix([0, i + 1, 2*i, i - 1, 0])
    [ [1.00...] + [+/- ...]*I  [3.141592653589793...] + [+/-...]*I]
    [ [+/- ...] + [+/- ...]*I  [1.000000000000000...] + [+/-...]*I]

Then we compute a connection matrix to the singularity itself::

    sage: dop.numerical_transition_matrix([0, i], 1e-10)
    [            ...           [+/-...] + [-0.50000000...]*I]
    [ ...1.000000...  [0.7853981634...] + [0.346573590...]*I]

Note that a path that crosses the branch cut of the complex logarithm
yields a different result::

    sage: dop.numerical_transition_matrix([0, i - 1, i], 1e-10)
    [     [+/-...] + [+/-...]*I         [+/-...] + [-0.5000000000...]*I]
    [ [1.00000...] + [+/-...]*I [-2.356194490...] + [0.3465735902...]*I]

In general, if the operator has rational coefficients, its singular
points are algebraic numbers. In connection problems such as the above,
they need to be specified exactly. Here is a way to do it::

    sage: dop = (x^2 - 2)*Dx^2 + x + 1
    sage: dop.numerical_transition_matrix([0, 1, QQbar(sqrt(2))], 1e-10)
    [         [2.49388146...] + [+/-...]*I          [2.40894178...] + [+/-...]*I]
    [[-0.203541775...] + [6.68738570...]*I  [0.204372067...] + [6.45961849...]*I]

The operator itself may be defined over a number field (with a complex
embedding)::

    sage: K.<zeta7> = CyclotomicField(7)
    sage: (Dx - zeta7).numerical_transition_matrix([0, 1])
    [[1.32375209616333...] + [1.31434281345999...]*I]

Some notable examples of incorrect input::

    sage: (Dx - 1).numerical_transition_matrix([])
    Traceback (most recent call last):
    ...
    ValueError: empty path

    sage: ((x - 1)*Dx + 1).numerical_transition_matrix([0, 2])
    Traceback (most recent call last):
    ...
    ValueError: Step 0 --> 2 passes through or too close to singular
    point 1 (to compute the connection to a singular point, make it a
    vertex of the path)

    sage: Dops.zero().numerical_transition_matrix([0, 1])
    Traceback (most recent call last):
    ...
    ValueError: operator must be nonzero
```


### `UnivariateEulerDifferentialOperatorOverUnivariateRing.to_D`  (differential operators (D))

```
Return the differential operator corresponding to ``self``

INPUT:

- ``alg`` -- the Ore algebra in which the output should be expressed.
  The algebra must satisfy ``alg.base_ring().base_ring() == self.base_ring().base_ring()``
  and ``alg.is_D()`` is not ``False``.
  Instead of an algebra object, also a string can be passed as argument.
  This amounts to specifying an Ore algebra over ``self.base_ring()`` with
  the standard derivation with respect to ``self.base_ring().gen()``.

EXAMPLES::

    sage: from ore_algebra import *
    sage: R.<x> = ZZ['x']
    sage: A.<Tx> = OreAlgebra(R, 'Tx')
    sage: (Tx^4).to_D(OreAlgebra(R, 'Dx'))
    x^4*Dx^4 + 6*x^3*Dx^3 + 7*x^2*Dx^2 + x*Dx
    sage: (Tx^4).to_D('Dx').to_T(A)
    Tx^4
```


### `UnivariateEulerDifferentialOperatorOverUnivariateRing.to_S`  (differential operators (D))

```
Return a recurrence operator annihilating the coefficient sequence of
every power series (at the origin) annihilated by ``self``.

INPUT:

- ``alg`` -- the Ore algebra in which the output should be expressed.
  The algebra must satisfy ``alg.base_ring().base_ring() == self.base_ring().base_ring()``
  and ``alg.is_S()`` is not ``False``.
  Instead of an algebra object, also a string can be passed as argument.
  This amounts to specifying an Ore algebra over ``self.base_ring()`` with
  the standard shift with respect to ``self.base_ring().gen()``.

EXAMPLES::

    sage: from ore_algebra import *
    sage: R.<x> = ZZ['x']
    sage: A.<Tx> = OreAlgebra(R, 'Tx')
    sage: R2.<n> = ZZ['n']
    sage: A2.<Sn> = OreAlgebra(R2, 'Sn')
    sage: (Tx - 1).to_S(A2)
    n - 1
    sage: ((1+x)*Tx^2 + Tx).to_S(A2)
    (n^2 + 3*n + 2)*Sn + n^2
    sage: ((x^3+x^2-x)*Tx + (x^2+1)).to_S(A2)
    Sn^3 + (-n - 2)*Sn^2 + (n + 2)*Sn + n
```


### `UnivariateRecurrenceOperatorOverUnivariateRing.to_D`  (recurrence operators (S))

```
Returns a differential operator which annihilates every power series whose
coefficient sequence is annihilated by ``self``.
The output operator may not be minimal.

INPUT:

- ``alg`` -- the Ore algebra in which the output should be expressed.
  The algebra must satisfy ``alg.base_ring().base_ring() == self.base_ring().base_ring()``
  and ``alg.is_D()`` is not ``False``.
  Instead of an algebra object, also a string can be passed as argument.
  This amounts to specifying an Ore algebra over ``self.base_ring()`` with
  the standard derivation with respect to ``self.base_ring().gen()``.

EXAMPLES::

  sage: from ore_algebra import *
  sage: Rn.<n> = ZZ['n']; Rx.<x> = ZZ['x']
  sage: A.<Sn> = OreAlgebra(Rn, 'Sn')
  sage: B.<Dx> = OreAlgebra(Rx, 'Dx')
  sage: (Sn - 1).to_D(B)
  (-x + 1)*Dx - 1
  sage: ((n+1)*Sn - 1).to_D(B)
  x*Dx^2 + (-x + 1)*Dx - 1
  sage: (x*Dx-1).to_S(A).to_D(B)
  x*Dx - 1
```


### `UnivariateRecurrenceOperatorOverUnivariateRing.to_T`  (recurrence operators (S))

```
Returns a differential operator, expressed in terms of the Euler derivation,
which annihilates every power series (about the origin) whose coefficient
sequence is annihilated by ``self``.
The output operator may not be minimal.

INPUT:

- ``alg`` -- the Ore algebra in which the output should be expressed.
  The algebra must satisfy ``alg.base_ring().base_ring() == self.base_ring().base_ring()``
  and ``alg.is_T()`` is not ``False``.
  Instead of an algebra object, also a string can be passed as argument.
  This amounts to specifying an Ore algebra over ``self.base_ring()`` with
  the Euler derivation with respect to ``self.base_ring().gen()``.

EXAMPLES::

  sage: from ore_algebra import *
  sage: Rn.<n> = ZZ['n']; Rx.<x> = ZZ['x']
  sage: A.<Sn> = OreAlgebra(Rn, 'Sn')
  sage: B.<Tx> = OreAlgebra(Rx, 'Tx')
  sage: (Sn - 1).to_T(B)
  (-x + 1)*Tx - x
  sage: ((n+1)*Sn - 1).to_T(B)
  Tx^2 - x*Tx - x
  sage: (x*Tx-1).to_S(A).to_T(B)
  x*Tx^2 + (x - 1)*Tx
```


### `UnivariateRecurrenceOperatorOverUnivariateRing.to_list`  (recurrence operators (S))

```
Computes the terms of some sequence annihilated by ``self``.

INPUT:

- ``init`` -- a vector (or list or tuple) of initial values.
  The components must be elements of ``self.base_ring().base_ring().fraction_field()``.
  If the length is more than ``self.order()``, we do not check whether the given
  terms are consistent with ``self``.
- ``n`` -- desired number of terms.
- ``start`` (optional) -- index of the sequence term which is represented
  by the first entry of ``init``. Defaults to zero.
- ``append`` (optional) -- if ``True``, the computed terms are appended
  to ``init`` list. Otherwise (default), a new list is created.
- ``padd`` (optional) -- if ``True``, the vector of initial values is implicitly
  prolonged to the left (!) by zeros if it is too short. Otherwise (default),
  the method raises a ``ValueError`` if ``init`` is too short.

OUTPUT:

A list of ``n`` terms whose `k` th component carries the sequence term with
index ``start+k``.
Terms whose calculation causes an error are represented by ``None``.

EXAMPLES::

   sage: from ore_algebra import *
   sage: R = ZZ['x']['n']; x = R('x'); n = R('n')
   sage: A.<Sn> = OreAlgebra(R, 'Sn')
   sage: L = ((n+2)*Sn^2 - x*(2*n+3)*Sn + (n+1))
   sage: L.to_list([1, x], 5)
   [1, x, (3*x^2 - 1)/2, (5*x^3 - 3*x)/2, (35*x^4 - 30*x^2 + 3)/8]
   sage: polys = L.to_list([1], 5, padd=True)
   sage: polys
   [1, x, (3*x^2 - 1)/2, (5*x^3 - 3*x)/2, (35*x^4 - 30*x^2 + 3)/8]
   sage: L.to_list([polys[3], polys[4]], 8, start=3)
   [(5*x^3 - 3*x)/2,
    (35*x^4 - 30*x^2 + 3)/8,
    (63*x^5 - 70*x^3 + 15*x)/8,
    (231*x^6 - 315*x^4 + 105*x^2 - 5)/16,
    (429*x^7 - 693*x^5 + 315*x^3 - 35*x)/16,
    (6435*x^8 - 12012*x^6 + 6930*x^4 - 1260*x^2 + 35)/128,
    (12155*x^9 - 25740*x^7 + 18018*x^5 - 4620*x^3 + 315*x)/128,
    (46189*x^10 - 109395*x^8 + 90090*x^6 - 30030*x^4 + 3465*x^2 - 63)/256]
   sage: ((n-5)*Sn - 1).to_list([1], 10)
   [1, 1/-5, 1/20, 1/-60, 1/120, -1/120, None, None, None, None]
```


### `UnivariateRecurrenceOperatorOverUnivariateRing.forward_matrix_bsplit`  (recurrence operators (S))

```
Uses division-free binary splitting to compute a product of ``n``
consecutive companion matrices of ``self``.

If ``self`` annihilates some sequence `c` of order `r`, this
allows rapidly computing `c_n, \ldots, c_{n+r-1}` (or just `c_n`)
without generating all the intermediate values.

INPUT:

- ``n`` -- desired number of terms to move forward
- ``start`` (optional) -- starting index. Defaults to zero.

OUTPUT:

A pair `(M, Q)` where `M` is an `r` by `r` matrix and `Q`
is a scalar, such that `M / Q` is the product of the companion
matrix at `n` consecutive indices.

We have `Q [c_{s+n}, \ldots, c_{s+r-1+n}]^T = M [c_s, c_{s+1}, \ldots, c_{s+r-1}]^T`,
where `s` is the initial position given by ``start``.

EXAMPLES::

    sage: from ore_algebra import *
    sage: R = ZZ
    sage: Rx.<x> = R[]
    sage: Rxk.<k> = Rx[]
    sage: Rxks = OreAlgebra(Rxk, 'Sk')
    sage: ann = Rxks([1+k, -3*x - 2*k*x, 2+k])
    sage: initial = Matrix([[1], [x]])
    sage: M, Q = ann.forward_matrix_bsplit(5)
    sage: (M * initial).change_ring(QQ['x']) / Q
    [               63/8*x^5 - 35/4*x^3 + 15/8*x]
    [231/16*x^6 - 315/16*x^4 + 105/16*x^2 - 5/16]

    sage: Matrix([[legendre_P(5, x)], [legendre_P(6, x)]])
    [               63/8*x^5 - 35/4*x^3 + 15/8*x]
    [231/16*x^6 - 315/16*x^4 + 105/16*x^2 - 5/16]


    sage: Sk = Rxks.gen()
    sage: (Sk^2 - 1).forward_matrix_param_rectangular(1, 10)
    (
    [1 0]
    [0 1], 1
    )

TODO: this should detect if the base coefficient ring is QQ (etc.)
and then switch to ZZ (etc.) internally.
```


### `UnivariateRecurrenceOperatorOverUnivariateRing.annihilator_of_sum`  (recurrence operators (S))

```
Returns an operator `L` which annihilates all the indefinite sums `\sum_{k=0}^n a_k`
where `a_n` runs through the sequences annihilated by ``self``.
The output operator is not necessarily of smallest possible order.

EXAMPLES::

   sage: from ore_algebra import *
   sage: R.<x> = ZZ['x']
   sage: A.<Sx> = OreAlgebra(R, 'Sx')
   sage: ((x+1)*Sx - x).annihilator_of_sum() # constructs L such that L(H_n) == 0
   (x + 2)*Sx^2 + (-2*x - 3)*Sx + x + 1
```


### `UnivariateRecurrenceOperatorOverUnivariateRing.annihilator_of_composition`  (recurrence operators (S))

```
Returns an operator `L` which annihilates all the sequences `f(floor(a(n)))`
where `f` runs through the functions annihilated by ``self``.
The output operator is not necessarily of smallest possible order.

INPUT:

- ``a`` -- a polynomial `u*x+v` where `x` is the generator of the base ring,
  `u` and `v` are integers or rational numbers. If they are rational,
  the base ring of the parent of ``self`` must contain ``QQ``.
- ``solver`` (optional) -- a callable object which applied to a matrix
  with polynomial entries returns its kernel.

EXAMPLES::

  sage: from ore_algebra import *
  sage: R.<x> = QQ['x']
  sage: A.<Sx> = OreAlgebra(R, 'Sx')
  sage: ((2+x)*Sx^2-(2*x+3)*Sx+(x+1)).annihilator_of_composition(2*x+5)
  (16*x^3 + 188*x^2 + 730*x + 936)*Sx^2 + (-32*x^3 - 360*x^2 - 1340*x - 1650)*Sx + 16*x^3 + 172*x^2 + 610*x + 714
  sage: ((2+x)*Sx^2-(2*x+3)*Sx+(x+1)).annihilator_of_composition(1/2*x)
  (x^2 + 11*x + 30)*Sx^6 + (-3*x^2 - 25*x - 54)*Sx^4 + (3*x^2 + 17*x + 26)*Sx^2 - x^2 - 3*x - 2
  sage: ((2+x)*Sx^2-(2*x+3)*Sx+(x+1)).annihilator_of_composition(100-x)
  (-x + 99)*Sx^2 + (2*x - 199)*Sx - x + 100
```


### `UnivariateRecurrenceOperatorOverUnivariateRing.annihilator_of_interlacing`  (recurrence operators (S))

```
Returns an operator `L` which annihilates any sequence which can be
obtained by interlacing sequences annihilated by ``self`` and the
operators given in the arguments.

More precisely, if ``self`` and the operators given in the arguments are
denoted `L_1,L_2,\dots,L_m`, and if `f_1(n),\dots,f_m(n)` are some
sequences such that `L_i` annihilates `f_i(n)`, then the output operator
`L` annihilates sequence
`f_1(0),f_2(0),\dots,f_m(0),f_1(1),f_2(1),\dots,f_m(1),\dots`, the
interlacing sequence of `f_1(n),\dots,f_m(n)`.

The output operator is not necessarily of smallest possible order.

The ``other`` operators must be coercible to the parent of ``self``.

EXAMPLES::

  sage: from ore_algebra import *
  sage: R.<x> = QQ['x']
  sage: A.<Sx> = OreAlgebra(R, 'Sx')
  sage: (x*Sx - (x+1)).annihilator_of_interlacing(Sx - (x+1), Sx + 1)
  (x^3 + 17/2*x^2 + 5/2*x - 87/2)*Sx^9 + (-1/3*x^4 - 11/2*x^3 - 53/2*x^2 - 241/6*x + 14)*Sx^6 + (7/2*x^2 + 67/2*x + 205/2)*Sx^3 + 1/3*x^4 + 13/2*x^3 + 77/2*x^2 + 457/6*x + 45
```


### `UnivariateRecurrenceOperatorOverUnivariateRing.generalized_series_solutions`  (recurrence operators (S))

```
Returns the generalized series solutions of this operator.

These are solutions of the form

  `(x/e)^{x u/v}\rho^x\exp\bigl(c_1 x^{1/m} +...+ c_{v-1} x^{1-1/m}\bigr)x^\alpha p(x^{-1/m},\log(x))`

where

* `e` is Euler's constant (2.71...)
* `v` is a positive integer
* `u` is an integer; the term `(x/e)^(v/u)` is called the "superexponential part" of the solution
* `\rho` is an element of an algebraic extension of the coefficient field `K`
  (the algebra's base ring's base ring); the term `\rho^x` is called the "exponential part" of
  the solution
* `c_1,...,c_{v-1}` are elements of `K(\rho)`; the term `\exp(...)` is called the "subexponential
  part" of the solution
* `m` is a positive integer multiple of `v`, it is called the object's "ramification"
* `\alpha` is an element of some algebraic extension of `K(\rho)`; the term `n^\alpha` is called
  the "polynomial part" of the solution (even if `\alpha` is not an integer)
* `p` is an element of `K(\rho)(\alpha)[[x]][y]`. It is called the "expansion part" of the solution.

An operator of order `r` has exactly `r` linearly independent solutions of this form.
This method computes them all, unless the flags specified in the arguments rule out
some of them.

Generalized series solutions are asymptotic expansions of sequences annihilated by the operator.

At present, the method only works for operators where `K` is some field which supports
coercion to ``QQbar``.

INPUT:

- ``n`` (default: 5) -- minimum number of terms in the expansions parts to be computed.
- ``dominant_only`` (default: False) -- if set to True, only compute solution(s) with maximal
  growth.
- ``real_only`` (default: False) -- if set to True, only compute solution(s) where `\rho,c_1,...,c_{v-1},\alpha`
  are real.
- ``infolevel`` (default: 0) -- if set to a positive integer, the methods prints some messages
  about the progress of the computation.

OUTPUT:

- a list of ``DiscreteGeneralizedSeries`` objects forming a fundamental system for this operator.

EXAMPLES::

  sage: from ore_algebra import *
  sage: R.<n> = QQ['n']; A.<Sn> = OreAlgebra(R, 'Sn')
  sage: (Sn - (n+1)).generalized_series_solutions()
  [(n/e)^n*n^(1/2)*(1 + 1/12*n^(-1) + 1/288*n^(-2) - 139/51840*n^(-3) - 571/2488320*n^(-4) + O(n^(-5)))]
  sage: list(map(Sn - (n+1), _))
  [0]

  sage: L = ((n+1)*Sn - n).annihilator_of_sum().symmetric_power(2)
  sage: L.generalized_series_solutions()
  [1 + O(n^(-5)),
   (1 + O(n^(-5)))*log(n) + 1/2*n^(-1) - 1/12*n^(-2) + 1/120*n^(-4) + O(n^(-5)),
   (1 + O(n^(-5)))*log(n)^2 + (n^(-1) - 1/6*n^(-2) + 1/60*n^(-4) + O(n^(-5)))*log(n) + 1/4*n^(-2) - 1/12*n^(-3) + 1/144*n^(-4) + O(n^(-5))]
  sage: list(map(L, _))
  [0, 0, 0]

  sage: L = n^2*(1-2*Sn+Sn^2) + (n+1)*(1+Sn+Sn^2)
  sage: L.generalized_series_solutions() # long time (1.4 s)
  [exp(3.464101615137755?*I*n^(1/2))*n^(1/4)*(1 - 2.056810333988042?*I*n^(-1/2) - 1107/512*n^(-2/2) + (0.?e-19 + 1.489453749877895?*I)*n^(-3/2) + 2960239/2621440*n^(-4/2) + (0.?e-19 - 0.926161373412572?*I)*n^(-5/2) - 16615014713/46976204800*n^(-6/2) + (0.?e-20 + 0.03266142931818572?*I)*n^(-7/2) + 16652086533741/96207267430400*n^(-8/2) + (0.?e-20 - 0.1615093987591473?*I)*n^(-9/2) + O(n^(-10/2))), exp(-3.464101615137755?*I*n^(1/2))*n^(1/4)*(1 + 2.056810333988042?*I*n^(-1/2) - 1107/512*n^(-2/2) + (0.?e-19 - 1.489453749877895?*I)*n^(-3/2) + 2960239/2621440*n^(-4/2) + (0.?e-19 + 0.926161373412572?*I)*n^(-5/2) - 16615014713/46976204800*n^(-6/2) + (0.?e-20 - 0.03266142931818572?*I)*n^(-7/2) + 16652086533741/96207267430400*n^(-8/2) + (0.?e-20 + 0.1615093987591473?*I)*n^(-9/2) + O(n^(-10/2)))]

  sage: L = guess([(-3)^k*(k+1)/(2*k+4) - 2^k*k^3/(k+3) for k in range(500)], A)
  sage: L.generalized_series_solutions()
  [2^n*n^2*(1 - 3*n^(-1) + 9*n^(-2) - 27*n^(-3) + 81*n^(-4) + O(n^(-5))), (-3)^n*(1 - n^(-1) + 2*n^(-2) - 4*n^(-3) + 8*n^(-4) + O(n^(-5)))]
  sage: L.generalized_series_solutions(dominant_only=True)
  [(-3)^n*(1 - n^(-1) + 2*n^(-2) - 4*n^(-3) + 8*n^(-4) + O(n^(-5)))]

TESTS::

    sage: rop = (-8 -12*Sn + (n^2+5*n+6)*Sn^3)
    sage: rop
    (n^2 + 5*n + 6)*Sn^3 - 12*Sn - 8
    sage: rop.generalized_series_solutions(1) # long time (7 s)
    [(n/e)^(-2/3*n)*2^n*exp(3*n^(1/3))*n^(-2/3)*(1 + 3/2*n^(-1/3) + 9/8*n^(-2/3) + O(n^(-3/3))),
    (n/e)^(-2/3*n)*(-1.000000000000000? + 1.732050807568878?*I)^n*exp((-1.500000000000000? + 2.598076211353316?*I)*n^(1/3))*n^(-2/3)*(1 + (-0.750000000000000? - 1.299038105676658?*I)*n^(-1/3) + (-0.562500000000000? + 0.974278579257494?*I)*n^(-2/3) + O(n^(-3/3))),
    (n/e)^(-2/3*n)*(-1.000000000000000? - 1.732050807568878?*I)^n*exp((-1.500000000000000? - 2.598076211353316?*I)*n^(1/3))*n^(-2/3)*(1 + (-0.750000000000000? + 1.299038105676658?*I)*n^(-1/3) + (-0.562500000000000? - 0.974278579257494?*I)*n^(-2/3) + O(n^(-3/3)))]
```


### `UnivariateDifferenceOperatorOverUnivariateRing.to_S`  (recurrence operators (S))

```
Returns the differential operator corresponding to ``self``

INPUT:

- ``alg`` -- the Ore algebra in which the output should be expressed.
  The algebra must satisfy ``alg.base_ring().base_ring() == self.base_ring().base_ring()``
  and ``alg.is_S()`` is not ``False``.
  Instead of an algebra object, also a string can be passed as argument.
  This amounts to specifying an Ore algebra over ``self.base_ring()`` with
  a standard shift with respect to ``self.base_ring().gen()``.

EXAMPLES::

  sage: from ore_algebra import *
  sage: R.<x> = ZZ['x']
  sage: A.<Fx> = OreAlgebra(R, 'Fx')
  sage: (Fx^4).to_S(OreAlgebra(R, 'Sx'))
  Sx^4 - 4*Sx^3 + 6*Sx^2 - 4*Sx + 1
  sage: (Fx^4).to_S('Sx')
  Sx^4 - 4*Sx^3 + 6*Sx^2 - 4*Sx + 1
```


### `UnivariateDifferenceOperatorOverUnivariateRing.to_D`  (recurrence operators (S))

```
Returns a differential operator which annihilates every power series (about
the origin) whose coefficient sequence is annihilated by ``self``.
The output operator may not be minimal.

INPUT:

- ``alg`` -- the Ore algebra in which the output should be expressed.
  The algebra must satisfy ``alg.base_ring().base_ring() == self.base_ring().base_ring()``
  and ``alg.is_D()`` is not ``False``.
  Instead of an algebra object, also a string can be passed as argument.
  This amounts to specifying an Ore algebra over ``self.base_ring()`` with
  the standard derivation with respect to ``self.base_ring().gen()``.

EXAMPLES::

  sage: from ore_algebra import *
  sage: Rn.<n> = ZZ['n']; Rx.<x> = ZZ['x']
  sage: A.<Fn> = OreAlgebra(Rn, 'Fn')
  sage: B.<Dx> = OreAlgebra(Rx, 'Dx')
  sage: Fn.to_D(B)
  (-x + 1)*Dx - 1
  sage: ((n+1)*Fn - 1).to_D(B)
  (-x^2 + x)*Dx^2 + (-4*x + 1)*Dx - 2
  sage: (x*Dx-1).to_F(A).to_D(B)
  x*Dx - 1
```


### `UnivariateDifferenceOperatorOverUnivariateRing.to_T`  (recurrence operators (S))

```
Returns a differential operator, expressed in terms of the Euler derivation,
which annihilates every power series (about the origin) whose coefficient
sequence is annihilated by ``self``.
The output operator may not be minimal.

INPUT:

- ``alg`` -- the Ore algebra in which the output should be expressed.
  The algebra must satisfy ``alg.base_ring().base_ring() == self.base_ring().base_ring()``
  and ``alg.is_T()`` is not ``False``.
  Instead of an algebra object, also a string can be passed as argument.
  This amounts to specifying an Ore algebra over ``self.base_ring()`` with
  the Euler derivation with respect to ``self.base_ring().gen()``.

EXAMPLES::

  sage: from ore_algebra import *
  sage: Rn.<n> = ZZ['n']; Rx.<x> = ZZ['x']
  sage: A.<Fn> = OreAlgebra(Rn, 'Fn')
  sage: B.<Tx> = OreAlgebra(Rx, 'Tx')
  sage: Fn.to_T(B)
  (-x + 1)*Tx - x
  sage: ((n+1)*Fn - 1).to_T(B)
  (-x + 1)*Tx^2 - 3*x*Tx - 2*x
  sage: (x*Tx-1).to_F(A).to_T(B)
  x*Tx^2 + (x - 1)*Tx
```
