<!-- Vendored from https://github.com/flintlib/python-flint/blob/0.8.0/doc/source/general.rst (python-flint 0.8.0) and https://python-flint.readthedocs.io/en/latest/ class-intro sections for fmpz/fmpq/fmpz_poly/nmod/arb/acb (docs version 0.9.0, nearest to installed 0.8.0); method lists abridged to names only -->
# General concepts

## Importing

The `flint` module exposes a set of distinctly-named types together with
a small number of top-level functions and objects. Most functionality is
provided as methods on the types. This means that there should be no
namespace conflicts with most user code, with Python's builtin `math`
and `cmath` modules, or with packages such as `gmpy`, `numpy`, `sympy`
and `mpmath`. For typical interactive use, it should therefore generally
be safe to `import *`:

> \>\>\> from flint import \* \>\>\> fmpq(3) / 2 3/2

For non-interactive use, it is still good manners to use explicit
imports or preserve the `flint` namespace prefix:

    >>> import flint
    >>> flint.fmpq(3) / 2
    3/2

## Global context

Various settings are controlled by a global context object, `flint.ctx`.
Printing this object in the REPL shows the current settings, with a
brief explanation of each parameter:

    >>> from flint import ctx
    >>> ctx
    pretty = True      # pretty-print repr() output
    unicode = False    # use unicode characters in output
    prec = 53          # real/complex precision (in bits)
    dps = 15           # real/complex precision (in digits)
    cap = 10           # power series precision
    threads = 1        # max number of threads used internally

The user can mutate the properties directly, for example:

    >>> ctx.pretty = False
    >>> fmpq(3,2)
    fmpq(3,2)
    >>> ctx.pretty = True
    >>> fmpq(3,2)
    3/2

Calling `ctx.default()` restores the default settings.

The special method `ctx.cleanup()` frees up internal caches used by
MPFR, FLINT and Arb. The user does normally not have to worry about
this.

The context object `flint.ctx` can be controlled locally to increase the
working precision using python context managers:

    >>> arb(2).sqrt()
    [1.41421356237309 +/- 5.15e-15]
    >>> with ctx.extraprec(15):
    ...     arb(2).sqrt()
    ...
    [1.414213562373095049 +/- 2.10e-19]

In the same manner, it is possible to exactly set the working precision,
or to update it in terms of digits:

    >>> with ctx.extradps(15):
    ...     arb(2).sqrt()
    ...
    [1.41421356237309504880168872421 +/- 6.27e-31]
    >>> with ctx.workprec(15):
    ...     arb(2).sqrt()
    ...
    [1.414 +/- 2.46e-4]

## Types and methods

As a general rule, C functions associated with a type in FLINT or Arb
are exposed as methods of the corresponding Python type.

For example, there is both an `.fmpq.bernoulli` (which computes a
Bernoulli number as an exact fraction) and `.arb.bernoulli` (which
computes a Bernoulli number as an approximate real number).

A function that transforms a single value to the same type is usually an
ordinary method of that type, for instance `.arb.exp`. A function with a
different signature can either provided as a static method that takes
all inputs as function arguments, or as a method of the "primary" input,
taking the other inputs as arguments to the method (for example
`.arb.bessel_j`).

When a method involves different types for inputs and outputs (or just
among the inputs), it will typically be a method of the more "complex"
type. For example, a matrix type is more "complex" than the underlying
scalar type, so `.fmpz_mat.det` is a method of the matrix type,
returning a scalar, and not vice versa.

The method-based interface is intended to keep the code simple, not to
be aesthetically pleasing to mathematicians. A functional top-level
interface might be added in the future, allowing more idiomatic
mathematical notation (for example, `exp` and `det` as regular
functions).

## Mutability

Objects have immutable semantics. For example, the second line in:

    b = a
    a += c

leaves *b* unchanged.

However, mutation via direct element access is supported for matrices
and polynomials. Some methods also allow explicitly performing the
operation in-place. Civilized users will restrict their use of such
methods to the point in the code where the object is first constructed:

    def create_thing():   # ok
        a = thing()
        a.mutate()
        return a

## Crashing and burning

Very little overflow checking is done ahead-of-time. Trying to compute
an object far too large to hold in memory (for example, the exact
factorial of <span class="title-ref">2^{64}-1</span>) will likely abort
the process, instead of raising an `OverflowError` or `MemoryError` that
can be caught at the Python level.

Input that is obviously *invalid* (for example a negative number passed
as a length) can also cause crashes or worse things to happen. Ideally,
bad input should be caught at the Python level and result in appropriate
exceptions being raised, but this is not yet done systematically. At
this time, users should assume that invalid input leads to undefined
behavior!

## Inexact numbers and numerical evaluation

Real and complex numbers are represented by midpoint-radius intervals
(balls). All operations on real and complex numbers output intervals
representing rigorous error bounds. This also extends to polynomials and
matrices of real and complex numbers.

The working precision for real and complex arithmetic is controlled by
the global context object attributes `ctx.prec` (in bits) `ctx.dps` (in
decimal digits). Changing either attribute changes the other to match.

Be careful about using Python float and complex literals as input. Doing
`arb(0.1)` actually gives an interval containing the rational number

> 3602879701896397 times 2^{-55} =
> 0.1000000000000000055511151231257827021181583404541015625

which might not be what you want. Do `arb("0.1")`, `arb("1/10")` or
`arb(fmpq(1,10))` if you want the correct decimal fraction. Small
integers and power-of-two denominators are still safe, for example
`arb(100.25)`.

Pointwise boolean predicates (such as the usual comparison operators)
involving inexact numbers return *True* only if the predicate certainly
is true (i.e. it holds for all combinations of points that can be chosen
from the set-valued inputs), and return *False* if the predicate either
definitely is false or the truth cannot be determined. To determine that
a predicate is definitely false, test both the predicate and the inverse
predicate, e.g. if either `x < y` or `y <= x` returns *True*, then the
other is definitely false; if both return *False*, then neither can be
determined from the available data.

The following convenience functions are provided for numerical
evaluation with adaptive working precision.

## Power series

Power series objects track the precision (the number of known terms)
automatically. The upper precision for power series is controlled by
`flint.ctx.cap`, with the default value 10.

> \>\>\> fmpq_series(\[0,1\]).exp() 1 + x + 1/2\*x^2 + 1/6\*x^3 +
> 1/24\*x^4 + 1/120\*x^5 + 1/720\*x^6 + 1/5040\*x^7 + 1/40320\*x^8 +
> 1/362880\*x^9 + O(x^10) \>\>\> ctx.cap = 4 \>\>\>
> fmpq_series(\[0,1\]).exp() 1 + x + 1/2\*x^2 + 1/6\*x^3 + O(x^4) \>\>\>
> ctx.cap = 10 \>\>\> fmpq_series(\[0,1\], prec=5).exp() 1 + x +
> 1/2\*x^2 + 1/6\*x^3 + 1/24\*x^4 + O(x^5)
>
> \>\>\> ctx.cap = 3 \>\>\> ctx.dps = 10 \>\>\>
> arb_series(\[1,3,4\]).exp() (\[2.718281828 +/- 4.79e-10\]) +
> (\[8.154845485 +/- 4.36e-10\])*x + (\[23.10539554 +/- 2.25e-9\])*x^2 +
> O(x^3) \>\>\> ctx.default()



# **fmpz** – integers¶

class flint.fmpz(*\*args*)¶  
The *fmpz* type represents an arbitrary-size integer.

    >>> fmpz(3) ** 25
    847288609443


Methods available on `fmpz` (see upstream docs for details):

    bell_number  bin_uiui  bit_length  divisor_sigma  euler_number  euler_phi
    fac_ui  factor  factor_smooth  fib_ui  gcd  height_bits
    is_perfect_power  is_prime  is_probable_prime  is_square  is_zero  isqrt
    jacobi  lcm  moebius_mu  partitions_p  primorial_ui  repr
    rising  root  sqrt  sqrtmod  sqrtrem  stirling_s1
    stirling_s2  str


# **fmpq** – rational numbers¶

class flint.fmpq(*\*args*)¶  
The fmpq type represents multiprecision rational numbers.

    >>> fmpq(1,7) + fmpq(50,51)
    401/357


Methods available on `fmpq` (see upstream docs for details):

    bernoulli  ceil  dedekind_sum  denom  floor  gcd
    harmonic  height_bits  is_zero  next  numer  repr
    round  sqrt  str  trunc


# **fmpz_poly** – polynomials over integers¶

class flint.fmpz_poly(*\*args*)¶  
The *fmpz_poly* type represents dense univariate polynomials over the
integers.

    >>> fmpz_poly([1,2,3]) ** 3
    27*x^6 + 54*x^5 + 63*x^4 + 44*x^3 + 21*x^2 + 6*x + 1
    >>> divmod(fmpz_poly([2,0,1,1,6]), fmpz_poly([3,5,7]))
    (0, 6*x^4 + x^3 + x^2 + 2)


Methods available on `fmpz_poly` (see upstream docs for details):

    chebyshev_t  chebyshev_u  coeffs  complex_roots  content  cos_minpoly
    cyclotomic  deflate  derivative  discriminant  factor  factor_squarefree
    gcd  height_bits  hilbert_class_poly  inflate  is_constant  is_cyclotomic
    is_gen  is_one  is_zero  leading_coefficient  left_shift  mul_low
    pow_trunc  real_roots  repr  resultant  right_shift  roots
    sqrt  str  swinnerton_dyer  truncate


# **nmod** – integers mod wordsize n¶

class flint.nmod(*val*, *mod*)¶  
The nmod type represents elements of Z/nZ for word-size n.

    >>> nmod(10,17) * 2
    3


Methods available on `nmod` (see upstream docs for details):

    is_zero  modulus  repr  sqrt  str


# **arb** – real numbers¶

class flint.arb(*mid=None*, *rad=None*)¶  
Represents a real number \\x\\ by a midpoint \\m\\ and a radius \\r\\
such that \\x \in \[m \pm r\] = \[m-r, m+r\]\\. The midpoint and radius
are both floating-point numbers. The radius uses a fixed,
implementation-defined precision (30 bits). The precision used for
midpoints is controlled by `ctx.prec` (bits) or equivalently `ctx.dps`
(digits).

The constructor accepts a midpoint *mid* and a radius *rad*, either of
which defaults to zero if omitted. The arguments can be tuples \\(a,
b)\\ representing exact floating-point data \\a 2^b\\, integers,
floating-point numbers, rational strings, or decimal strings. If the
radius is nonzero, it might be rounded up to a slightly larger value
than the exact value passed by the user.

    >>> arb(10.25)
    10.2500000000000
    >>> print(1 / arb(4))  # exact
    0.250000000000000
    >>> print(1 / arb(3))  # approximate
    [0.333333333333333 +/- 3.71e-16]
    >>> print(arb("3.0"))
    3.00000000000000
    >>> print(arb("0.1"))
    [0.100000000000000 +/- 2.23e-17]
    >>> print(arb("1/10"))
    [0.100000000000000 +/- 2.23e-17]
    >>> print(arb("3.14159 +/- 0.00001"))
    [3.1416 +/- 2.01e-5]
    >>> ctx.dps = 50
    >>> print(arb("1/3"))
    [0.33333333333333333333333333333333333333333333333333 +/- 3.78e-51]
    >>> ctx.default()

Converting to or from decimal results in some loss of accuracy. See
`arb.str()` for details.


Methods available on `arb` (see upstream docs for details):

    abs_lower  abs_upper  acos  acosh  agm  airy
    airy_ai  airy_ai_zero  airy_bi  airy_bi_zero  asin  asinh
    atan  atan2  atanh  backlund_s  bell_number  bernoulli
    bernoulli_poly  bessel_i  bessel_j  bessel_k  bessel_y  beta_lower
    bin  bin_uiui  bits  ceil  chebyshev_t  chebyshev_u
    chi  ci  const_catalan  const_e  const_euler  const_glaisher
    const_khinchin  const_log10  const_log2  const_sqrt_pi  contains  contains_integer
    contains_interior  cos  cos_pi  cos_pi_fmpq  cosh  cot
    cot_pi  coth  coulomb  coulomb_f  coulomb_g  csc
    csch  digamma  ei  erf  erfc  erfcinv
    erfi  erfinv  exp  expint  expm1  fac
    fac_ui  fib  floor  fmpq  fmpz  fresnel_c
    fresnel_s  gamma  gamma_fmpq  gamma_lower  gamma_upper  gegenbauer_c
    gram_point  hermite_h  hypgeom  hypgeom_0f1  hypgeom_1f1  hypgeom_2f1
    hypgeom_u  intersection  jacobi_p  laguerre_l  lambertw  legendre_p
    legendre_p_root  legendre_q  lgamma  li  log  log1p
    log_base  lower  man_exp  max  mid  mid_rad_10exp
    min  nan  neg  neg_inf  nonnegative_part  overlaps
    partitions_p  pi  polylog  pos_inf  rad  rel_accuracy_bits
    rel_one_accuracy_bits  repr  rgamma  rising  rising2  rising_fmpq_ui
    root  rsqrt  sec  sech  sgn  shi
    si  sin  sin_cos  sin_cos_pi  sin_cos_pi_fmpq  sin_pi
    sin_pi_fmpq  sinc  sinc_pi  sinh  sinh_cosh  sqrt
    str  tan  tan_pi  tanh  union  unique_fmpz
    upper  zeta  zeta_nzeros


# **acb** – complex numbers¶

class flint.acb(*real=None*, *imag=None*)¶  
An *acb* represents a complex number by a rectangular enclosure
consisting of *arb* balls for the real and imaginary parts.

    >>> from flint import fmpq
    >>> acb(2)
    2.00000000000000
    >>> acb(2+3j)
    2.00000000000000 + 3.00000000000000j
    >>> acb("2 +/- 0.001", fmpq(2,3))
    [2.00 +/- 1.01e-3] + [0.666666666666667 +/- 4.82e-16]j
    >>> acb(-1) ** 0.25
    [0.707106781186547 +/- 6.14e-16] + [0.707106781186547 +/- 6.15e-16]j


Methods available on `acb` (see upstream docs for details):

    abs_lower  abs_upper  acos  acosh  agm  airy
    airy_ai  airy_bi  arg  asin  asinh  atan
    atanh  barnes_g  bernoulli_poly  bessel_i  bessel_j  bessel_k
    bessel_y  beta_lower  bits  chebyshev_t  chebyshev_u  chi
    ci  complex_rad  conjugate  contains  contains_integer  contains_interior
    cos  cos_pi  cosh  cot  cot_pi  coth
    coulomb  coulomb_f  coulomb_g  csc  csch  csgn
    dft  digamma  dirichlet_eta  dirichlet_l  ei  elliptic_e
    elliptic_e_inc  elliptic_f  elliptic_inv_p  elliptic_invariants  elliptic_k  elliptic_p
    elliptic_pi  elliptic_pi_inc  elliptic_rc  elliptic_rd  elliptic_rf  elliptic_rg
    elliptic_rj  elliptic_roots  elliptic_sigma  elliptic_zeta  erf  erfc
    erfi  exp  exp_pi_i  expint  expm1  fresnel_c
    fresnel_s  gamma  gamma_lower  gamma_upper  gegenbauer_c  hermite_h
    hypgeom  hypgeom_0f1  hypgeom_1f1  hypgeom_2f1  hypgeom_u  integral
    jacobi_p  laguerre_l  lambertw  legendre_p  legendre_q  lerch_phi
    lgamma  li  log  log1p  log_barnes_g  log_sin_pi
    mid  modular_delta  modular_eta  modular_j  modular_lambda  modular_theta
    neg  overlaps  pi  polygamma  polylog  pow
    rad  real_abs  real_ceil  real_floor  real_heaviside  real_max
    real_min  real_sgn  real_sqrt  rel_accuracy_bits  rel_one_accuracy_bits  repr
    rgamma  rising  rising2  root  rsqrt  sec
    sech  sgn  shi  si  sin  sin_cos
    sin_cos_pi  sin_pi  sinc  sinc_pi  sinh  sinh_cosh
    spherical_y  sqrt  stieltjes  str  tan  tan_pi
    tanh  union  unique_fmpz  zeta  zeta_zero  zeta_zeros