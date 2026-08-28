<!-- Vendored from https://snappy.computop.org/ (SnapPy 3.3.2 documentation): tutorial, snappy module overview, selected Manifold class methods, censuses, and verify pages; converted to markdown -->

# Tutorial

The easiest way to learn to use SnapPy is to watch the screencasts
available on YouTube:

- Intro and quickstart: an 11 minute video with the basics: Part
  I and Part
  II.

- An hour-long demo Practical computation with hyperbolic
  3-manifolds, recorded at the Thurston
  Memorial Conference.

- The SnapPy 2.0 new feature demo.

- SnapPy, SageMath, and Docker are
  friends with
  associated materials (4 pages), including
  homework.

- Notes, problem sheets, and
  references from the LMS-CMI
  Research School in Warwick in 2017.

- Another hour-long demo Practical computations with hyperbolic
  3-manifolds given
  at ICERM in 2019.

The **key** thing to remember when using the SnapPy command shell window
is that you can explore objects using introspection and tab-completion:

    In [1]: Manifold? <hit return-key>
    ...instructions for creating a manifold...

So now we create a manifold:

    In [2]: M = Manifold("m004")

But what can we do with it?

    In [3]: M.<hit tab-key>
    ...list of methods...

What does the “cover” method do?

    In [4]: M.cover? <hit return-key>
    ...description of cover method..

# The snappy module and its classes

SnapPy is centered around a Python interface for SnapPea called
“snappy”, and this is what you’re interacting with in the main “SnapPy
command shell” window. The main class is Manifold, which is an ideal
triangulation of the interior of a compact 3-manifold with torus
boundary, where each tetrahedron has been assigned the geometry of an
ideal tetrahedron in hyperbolic 3-space. A Dehn-filling can be specified
for each boundary component, allowing the description of closed
3-manifolds and some orbifolds. The class Manifold is derived from the
simpler Triangulation class which lacks any geometric structure. There
are also some additional classes for things like fundamental groups,
Dirichlet domains, etc. Snappy comes with a large library of
3-manifolds, some of which are grouped together in censuses.

- Manifold: the main class
  - `Manifold`
- ManifoldHP: High-precision variant
  - FAQ
- Triangulation
  - `Triangulation`
- Additional Classes
  - AbelianGroup
  - FundamentalGroup
  - SymmetryGroup
  - DirichletDomain
  - CuspNeighborhood
- Census manifolds
  - `OrientableCuspedCensus`
  - `OrientableClosedCensus`
  - `CensusKnots`
  - `LinkExteriors`
  - `HTLinkExteriors`
  - `RibbonLinks`
  - `NonorientableCuspedCensus`
  - `NonorientableClosedCensus`
  - Censuses of Platonic manifolds
  - `ManifoldTable`
  - `AlternatingKnotExteriors`
  - `NonalternatingKnotExteriors`

# Manifold: the main class

*class *snappy.Manifold  
A Manifold is a
`Triangulation`
together with a geometric structure. That is, a Manifold is an ideal
triangulation of the interior of a compact 3-manifold with torus and
Klein-bottle boundary components, where each tetrahedron has been
assigned the geometry of an ideal tetrahedron in hyperbolic 3-space. A
Dehn-filling can be specified for each boundary component, allowing the
description of closed 3-manifolds, some orbifolds and cone 3-manifolds.
Here’s a quick example:

    >>> M = Manifold('9_42')
    >>> M.volume()
    4.05686022
    >>> M.cusp_info('shape')
    [-4.278936315 + 1.95728679*I]

This is an example for running SnapPy inside Sage:

    sage: import snappy
    sage: M = snappy.Manifold('m125(1,2)(4,5)')
    sage: M.is_orientable()
    True

An alternative way of running SnapPy inside Sage:

    sage: from snappy import *
    sage: M = Manifold('m123')
    sage: M.num_cusps()
    1

A Manifold can be specified in a number of ways, e.g.

- Manifold(‘9_42’) : The complement of the knot 9_42 in S^3.

- Manifold(‘m125(1,2)(4,5)’) : The SnapPea census manifold m125 where
  the first cusp has Dehn filling (1,2) and the second cusp has filling
  (4,5).

- Manifold() : Opens a link editor window where can you specify a link
  complement.

In general, the specification can be from among the below, with
information on Dehn fillings added.

- SnapPea cusped census manifolds: e.g. ‘m123’, ‘s123’, ‘v123’.

- Link complements:

  > - Rolfsen’s table: e.g. ‘4_1’, ‘04_1’, ‘5^2_6’, ‘6_4^7’, ‘L20935’,
  >   ‘l104001’.
  >
  > - Hoste-Thistlethwaite Knotscape table: e.g. ‘11a17’ or ‘12n345’
  >
  > - Callahan-Dean-Weeks-Champanerkar-Kofman-Patterson knots: e.g.
  >   ‘K6_21’.
  >
  > - Dowker-Thistlethwaite code: e.g. ‘DT:\[(6,8,2,4)\]’

- Once-punctured torus bundles: e.g. ‘b++LLR’, ‘b+-llR’, ‘bo-RRL’,
  ‘bn+LRLR’

- Fibered manifold associated to a braid: ‘Braid\[1,2,-3,4\]’

  Here, the braid is thought of as a mapping class of the punctured
  disc, and this manifold is the corresponding mapping torus. If you
  want the braid closure, do (1,0) filling of the last cusp.

- From mapping class group data using Twister:

  ‘Bundle(S\_{1,1}, \[a0, B1\])’ or ‘Splitting(S\_{1,0}, \[b1, A0\],
  \[a0,B1\])’

  See the help for the ‘twister’ module for more.

- A SnapPea triangulation or link projection file: ‘filename’

  The file will be loaded if found in the current directory or the path
  given by the shell variable `SNAPPEA_MANIFOLD_DIRECTORY`. See
  `Manifold.save()` for
  details.

- A string containing the contents of a SnapPea triangulation or link
  projection file.

chern_simons(*accuracy=False*)  
Returns the Chern-Simons invariant of the manifold (normalized by
dividing it by \\2 \pi^2\\), if it is known.

    >>> M = Manifold('m015')
    >>> M.chern_simons()
    -0.15320413

The return value has an extra attribute, accuracy, which is the number
of digits of accuracy as *estimated* by SnapPea.

    >>> cs, accuracy = M.chern_simons(accuracy = True)
    >>> accuracy in (8, 9, 56, 57) # Low and High precision
    True

By default, when the manifold has at least one cusp, Zickert’s algorithm
is used; when the manifold is closed we use SnapPea’s original
algorithm, which is based on Meyerhoff-Hodgson-Neumann.

Note: When computing the Chern-Simons invariant of a closed manifold,
one must sometimes compute it first for the unfilled manifold so as to
initialize SnapPea’s internals. For instance,

    >>> M = Manifold('5_2')
    >>> M.chern_simons()
    -0.15320413
    >>> M.dehn_fill( (1,2) )
    >>> M.chern_simons()
    0.07731787

works, but will fail with
`ValueError:`` ``The`` ``Chern-Simons`` ``invariant`` ``isn't`` ``currently`` ``known.`
if the first call to chern_simons is not made.

complex_volume(*verified_modulo_2_torsion=False*, *bits_prec=None*)  
Returns the complex volume modulo \\i \pi^2\\ which is given by

\\\text{vol} + i \text{CS}\\

where \\\text{CS}\\ is the (unnormalized) Chern-Simons invariant.

    >>> M = Manifold('5_2')
    >>> M.complex_volume()
    2.82812209 - 3.02412838*I

Note that
`chern_simons`
normalizes the Chern-Simons invariant by dividing it by \\2 \pi^2 =
19.7392...\\

    >>> M.chern_simons()
    -0.153204133297152

More examples:

    >>> M.dehn_fill((1,2))
    >>> M.complex_volume()
    2.22671790 + 1.52619361*I
    >>> M = Manifold("3_1") # A non-hyperbolic example.
    >>> cvol = M.complex_volume()
    >>> cvol.real()
    0
    >>> cvol.imag()
    -1.64493407

If no cusp is filled or there is only one cusped (filled or unfilled),
the complex volume can be verified up to multiples of \\i \pi^2 /2\\ by
passing `verified_modulo_2_torsion`` ``=`` ``True` when inside SageMath.
Higher precision can be requested with `bits_prec`:

    sage: M = Manifold("m015")
    sage: M.complex_volume(verified_modulo_2_torsion=True, bits_prec = 93) # doctest: +NUMERIC21
    2.828122088330783162764? + 1.910673824035377649698?*I
    sage: M = Manifold("m015(3,4)")
    sage: M.complex_volume(verified_modulo_2_torsion=True) # doctest: +NUMERIC6
    2.625051576? - 0.537092383?*I

cover(*permutation_rep*) → snappy.Manifold  
Returns a `Manifold` representing
the finite cover specified by a transitive permutation representation.
The representation is specified by a list of permutations, one for each
generator of the simplified presentation of the fundamental group. Each
permutation is specified as a list `P` such such that
`set(P)`` ``==`` ``set(range(d))` where `d` is the degree of the cover.

    >>> M = Manifold('m004')
    >>> N0 = M.cover([[1, 3, 0, 4, 2], [0, 2, 1, 4, 3]])
    >>> abs(N0.volume()/M.volume() - 5) < 0.0000000001
    True

If within SageMath, the permutations can also be of type
`PermutationGroupElement`, in which case they act on the set
`range(1,`` ``d`` ``+`` ``1)`. Or, you can specify a GAP or Magma
subgroup of the fundamental group. Some examples:

    sage: M = Manifold('m004')

The basic method:

    sage: N0 = M.cover([[1, 3, 0, 4, 2], [0, 2, 1, 4, 3]])

From a Gap subgroup:

    sage: G = gap(M.fundamental_group())
    sage: H = G.LowIndexSubgroupsFpGroup(5)[9]
    sage: N1 = M.cover(H)
    sage: N0 == N1
    True

Or a homomorphism to a permutation group:

    sage: f = G.GQuotients(PSL(2,7))[1]
    sage: N2 = M.cover(f)
    sage: N2.volume()/M.volume() # doctest: +NUMERIC9
    8.00000000

Or maybe we want larger cover coming from the kernel of this:

    sage: N3 = M.cover(f.Kernel())
    sage: N3.volume()/M.volume() # doctest: +NUMERIC9
    168.00000000

Check the homology against what Gap computes directly:

    sage: N3.homology().betti_number()
    32
    sage: len([ x for x in f.Kernel().AbelianInvariants().sage() if x == 0])
    32

We can do the same for Magma:

    sage: G = magma(M.fundamental_group())             #doctest: +SKIP
    sage: Q, f = G.pQuotient(5, 1, nvals = 2)          #doctest: +SKIP
    sage: M.cover(f.Kernel()).volume()                 #doctest: +SKIP
    10.14941606
    sage: h = G.SimpleQuotients(1, 11, 2, 10000)[1,1]  #doctest: +SKIP
    sage: N4 = M.cover(h)                              #doctest: +SKIP
    sage: N2 == N4                                     #doctest: +SKIP
    True

cover_info()  
If this is a manifold or triangulation which was constructed as a
covering space, return a dictionary describing the cover. Otherwise
return 0. The dictionary keys are ‘base’, ‘type’ and ‘degree’.

covers(*degree*, *method: Optional\[str\] = None*, *cover_type: str = 'all'*) → list\[snappy.Manifold\]  
Returns a list of `Manifold`s
corresponding to all of the finite covers of the given degree. The
default method is ‘low_index’ for general covers and ‘snappea’ for
cyclic covers. The former uses Sim’s algorithm while the latter uses the
original Snappea algorithm.

WARNING: If the degree is large this might take a very, very, very long
time.

    >>> M = Manifold('m003')
    >>> covers = M.covers(4)
    >>> sorted(N.homology() for N in covers)
    [Z/3 + Z/15 + Z, Z/5 + Z + Z]

It is faster to look just at cyclic covers.

    >>> covers = M.covers(4, cover_type='cyclic')
    >>> [(N, N.homology()) for N in covers]
    [(m003~cyc~0(0,0), Z/3 + Z/15 + Z)]

Here we check that we get the same number of covers with the ‘snappea’
and ‘low_index’ methods.

    >>> M = Manifold('m125')
    >>> len(M.covers(5))
    19
    >>> len(M.covers(5, method='snappea'))
    19

If you are using Sage, you can use GAP to find the subgroups, which is
often much faster, by specifying the optional argument method = ‘gap’ If
you have Magma installed, you can used it to do the heavy lifting by
specifying method=’magma’.

cusp_info(*data_spec=None*, *verified=False*, *bits_prec=None*)  
Returns an info object containing information about the given cusp.
Usage:

    >>> M = Manifold('v3227(0,0)(1,2)(3,2)')
    >>> M.cusp_info(1)
    Cusp 1 : torus cusp with Dehn filling coefficients (M, L) = (1.0, 2.0)

To get more detailed information about the cusp, we do

    >>> c = M.cusp_info(0)
    >>> c.shape
    0.11044502 + 0.94677098*I
    >>> c.modulus
    -0.12155872 + 1.04204128*I
    >>> sorted(c.keys())
    ['filling', 'holonomies', 'holonomy_accuracy', 'index', 'is_complete', 'modulus', 'shape', 'shape_accuracy', 'topology']

Here ‘shape’ is the shape of the cusp, i.e. (longitude/meridian) and
‘modulus’ is its shape in the geometrically preferred basis, i.e. (
(second shortest translation)/(shortest translation)). For cusps that
are filled, one instead cares about the holonomies:

    >>> M.cusp_info(-1)['holonomies']
    (-0.59883089 + 1.09812548*I, 0.89824633 + 1.49440443*I)

The complex numbers returned for the shape and for the two holonomies
have an extra attribute, accuracy, which is SnapPea’s *estimate* of
their accuracy.

You can also get information about multiple cusps at once:

    >>> M.cusp_info()
    [Cusp 0 : complete torus cusp of shape 0.11044502 + 0.94677098*I,
     Cusp 1 : torus cusp with Dehn filling coefficients (M, L) = (1.0, 2.0),
     Cusp 2 : torus cusp with Dehn filling coefficients (M, L) = (3.0, 2.0)]
    >>> M.cusp_info('is_complete')
    [True, False, False]

The cusp shapes can be verified:

    sage: M = Manifold('m292')
    sage: M.cusp_info('shape', verified = True, bits_prec = 60) # doctest: +NUMERIC12
    [-0.1766049820997? + 1.2028208192855?*I,
     -0.1766049820997? + 1.2028208192855?*I]

dehn_fill(*filling_data*, *which_cusp=None*) → None  
Set the Dehn filling coefficients of the cusps. This can be specified in
the following ways, where the cusps are numbered by 0,1,…,(num_cusps -
1).

- Fill cusp 2:

      >>> M = Manifold('8^4_1')
      >>> M.dehn_fill((2,3), 2)
      >>> M
      8^4_1(0,0)(0,0)(2,3)(0,0)

- Fill the last cusp:

      >>> M.dehn_fill((1,5), -1)
      >>> M
      8^4_1(0,0)(0,0)(2,3)(1,5)

- Fill the first two cusps:

      >>> M.dehn_fill( [ (3,0), (1, -4) ])
      >>> M
      8^4_1(3,0)(1,-4)(2,3)(1,5)

- When there is only one cusp, there’s a shortcut

      >>> N = Manifold('m004')
      >>> N.dehn_fill( (-3,4) )
      >>> N
      m004(-3,4)

Does not return a new Manifold.

filled_triangulation(*cusps_to_fill='all'*) → snappy.Manifold  
Return a new Manifold where the specified cusps have been permanently
filled in.

Filling all the cusps results in a Triangulation rather than a Manifold,
since SnapPea can’t deal with hyperbolic structures when there are no
cusps.

Examples:

    >>> M = Manifold('m125(1,2)(3,4)')
    >>> N = M.filled_triangulation()
    >>> N.num_cusps()
    0

Filling cusps 0 and 2 :

    >>> M = Manifold('v3227(1,2)(3,4)(5,6)')
    >>> M.filled_triangulation([0,2])
    v3227_filled(3,4)

fundamental_group(*simplify_presentation: bool = True*, *fillings_may_affect_generators: bool = True*, *minimize_number_of_generators: bool = True*, *try_hard_to_shorten_relators: bool = True*) → HolonomyGroup  
Return a
`HolonomyGroup`
representing the fundamental group of the manifold, together with its
holonomy representation. If integer Dehn surgery parameters have been
set, then the corresponding peripheral elements are killed.

    >>> M = Manifold('m004')
    >>> G = M.fundamental_group()
    >>> G
    Generators:
       a,b
    Relators:
       aaabABBAb
    >>> G.peripheral_curves()
    [('ab', 'aBAbABab')]
    >>> G.SL2C('baaBA')
    [ 2.50000000 - 2.59807621*I -6.06217783 - 0.50000000*I]
    [ 0.86602540 - 2.50000000*I -4.00000000 + 1.73205081*I]

There are three optional arguments all of which default to True:

- simplify_presentation

- fillings_may_affect_generators

- minimize_number_of_generators

    >>> M.fundamental_group(False, False, False)
    Generators:
       a,b,c
    Relators:
       CbAcB
       BacA

homology() → AbelianGroup  
Returns an
`AbelianGroup`
representing the first integral homology group of the underlying (Dehn
filled) manifold.

    >>> M = Triangulation('m003')
    >>> M.homology()
    Z/5 + Z

identify(*extends_to_link=False*)  
Looks for the manifold in all of the SnapPy databases. For hyperbolic
manifolds this is done by searching for isometries:

    >>> M = Manifold('m125')
    >>> M.identify()
    [m125(0,0)(0,0), L13n5885(0,0)(0,0), ooct01_00000(0,0)(0,0)]

By default, there is no restriction on the isometries. One can require
that the isometry take meridians to meridians. This might return fewer
results:

    >>> M.identify(extends_to_link=True)
    [m125(0,0)(0,0), ooct01_00000(0,0)(0,0)]

For closed manifolds, extends_to_link doesn’t make sense because of how
the kernel code works:

    >>> C = Manifold("m015(1,2)")
    >>> C.identify()
    [m006(-5,2)]
    >>> C.identify(True)
    []

is_isometric_to(*other: Manifold \| ManifoldHP*, *return_isometries: bool = False*) → bool \| List\[Isometry\]  
Returns `True` if M and N are isometric, `False` if they not. A
`RuntimeError` is raised in cases where the SnapPea kernel fails to
determine either answer. (This is fairly common for closed manifolds.)

    >>> M = Manifold('m004')
    >>> N = Manifold('4_1')
    >>> K = Manifold('5_2')
    >>> M.is_isometric_to(N)
    True
    >>> N.is_isometric_to(K)
    False

We can also get a complete list of isometries between the two manifolds:

    >>> M = Manifold('5^2_1')  # The Whitehead link
    >>> N = Manifold('m129')
    >>> isoms = M.is_isometric_to(N, return_isometries = True)
    >>> isoms[6]  # Includes action on cusps
    0 -> 1  1 -> 0
    [1  2]  [-1 -2]
    [0 -1]  [ 0  1]
    Extends to link

Each transformation between cusps is given by a matrix which acts on the
left. That is, the two *columns* of the matrix give the image of the
meridian and longitude respectively. In the above example, the meridian
of cusp 0 is sent to the meridian of cusp 1.

Note: The answer `True` is rigorous, but the answer `False` may not be
as there could be numerical errors resulting in finding an incorrect
canonical triangulation.

is_orientable() → bool  
Return whether the underlying 3-manifold is orientable.

    >>> M = Triangulation('x124')
    >>> M.is_orientable()
    False

is_two_bridge() → bool  
If the manifold is the complement of a two-bridge knot or link in
\\S^3\\, then this method returns \\(p,q)\\ where \\p/q\\ is the
fraction describing the link. Otherwise, returns `False`.

    >>> M = Manifold('m004')
    >>> M.is_two_bridge()
    (2, 5)
    >>> M = Manifold('m016')
    >>> M.is_two_bridge()
    False

Note: An answer of `True` is rigorous, but not the answer `False`, as
there could be numerical errors resulting in finding an incorrect
canonical triangulation.

normal_surfaces(*algorithm='FXrays'*)  
All the vertex spun-normal surfaces in the current triangulation.

    >>> M = Manifold('m004')
    >>> M.normal_surfaces()
    [<Surface 0: [0, 0] [1, 2] (4, 1)>,
     <Surface 1: [0, 1] [1, 2] (4, -1)>,
     <Surface 2: [1, 2] [2, 1] (-4, -1)>,
     <Surface 3: [2, 2] [2, 1] (-4, 1)>]

num_cusps(*cusp_type='all'*) → int  
Return the total number of cusps. By giving the optional argument
‘orientable’ or ‘nonorientable’ it will only count cusps of that type.

    >>> M = Triangulation('m125')
    >>> M.num_cusps()
    2

num_tetrahedra() → int  
Return the number of tetrahedra in the triangulation.

    >>> M = Triangulation('m004')
    >>> M.num_tetrahedra()
    2

simplify(*passes_at_fours=6*)  
Try to simplify the triangulation by doing Pachner moves.

    >>> M = Triangulation('12n123')
    >>> M.simplify()

It does four kinds of moves that reduce the number of tetrahedra:

- 3 -\> 2 and 2 -\> 0 Pacher moves, which eliminate one or two
  tetrahedra respectively.

- On suitable valence-1 edges, does a 2 -\> 3 and then 2 -\> 0 move,
  which removes a tetrahedron and creates a new valence-1 edge.

- When a 2-simplex has two edges of valence-4 giving rise to the
  suspension of a pentagon, replace these 6 tetrahedra with a single
  edge of valence 5.

It also does random 4 -\> 4 moves in hopes of setting up a
simplfication. The argument passes_at_fours is the number of times it
goes through the valence-4 edges without progress before giving up.

solution_type(*enum=False*)  
Returns the type of the current solution to the gluing equations,
basically a summary of how degenerate the solution is. If the flag
`enum=True` is set, then an integer value is returned. The possible
answers are:

- 0: `not`` ``attempted`

- 1: `all`` ``tetrahedra`` ``positively`` ``oriented` aka
  *geometric_solution*

  Should correspond to a genuine hyperbolic structure.

- 2: `contains`` ``negatively`` ``oriented`` ``tetrahedra` aka
  *nongeometric solution*

  Probably corresponds to a hyperbolic structure but some simplices have
  reversed orientations.

- 3: `contains`` ``flat`` ``tetrahedra` (should be called
  `all`` ``tetrahedra`` ``flat`)

  All tetrahedra have shape in \\\mathbb{R} - \\0, 1\\\\.

- 4: `contains`` ``degenerate`` ``tetrahedra`

  Some shapes are close to \\\\0,1, \infty\\\\.

- 5: `unrecognized`` ``solution`` ``type`

- 6: `no`` ``solution`` ``found`

    >>> M = Manifold('m007')
    >>> M.solution_type()
    'all tetrahedra positively oriented'
    >>> M.dehn_fill( (3,1) )
    >>> M.solution_type()
    'contains negatively oriented tetrahedra'
    >>> M.dehn_fill( (3,-1) )
    >>> M.solution_type()
    'contains degenerate tetrahedra'

symmetry_group(*of_link: bool = False*) → SymmetryGroup  
Returns the symmetry group of the Manifold. If the flag “of_link” is
set, then it only returns symmetries that preserves the meridians.

verify_hyperbolicity(*verbose=False*, *bits_prec=None*, *holonomy=False*, *fundamental_group_args=\[\]*, *lift_to_SL=True*)  
Given an orientable SnapPy Manifold, verifies its hyperbolicity.

Similar to HIKMOT’s
`verify_hyperbolicity()`,
the result is either `(True,`` ``listOfShapeIntervals)` or
`(False,`` ``[])` if verification failed. `listOfShapesIntervals` is a
list of complex intervals (elements in sage’s `ComplexIntervalField`)
certified to contain the true shapes for the hyperbolic manifold.

Higher precision intervals can be obtained by setting `bits_prec`:

    sage: from snappy import Manifold
    sage: M = Manifold("m019")
    sage: M.verify_hyperbolicity() # doctest: +NUMERIC12
    (True, [0.780552527850? + 0.914473662967?*I, 0.780552527850? + 0.91447366296773?*I, 0.4600211755737? + 0.6326241936052?*I])

    sage: M = Manifold("t02333(3,4)")
    sage: M.verify_hyperbolicity() # doctest: +NUMERIC9
    (True, [2.152188153612? + 0.284940667895?*I, 1.92308491369? + 1.10360701507?*I, 0.014388591584? + 0.143084469681?*I, -2.5493670288? + 3.7453498408?*I, 0.142120333822? + 0.176540027036?*I, 0.504866865874? + 0.82829881681?*I, 0.50479249917? + 0.98036162786?*I, -0.589495705074? + 0.81267480427?*I])

One can instead get a holonomy representation associated to the verified
hyperbolic structure. This representation takes values in 2x2 matrices
with entries in the `ComplexIntervalField`:

    sage: M = Manifold("m004(1,2)")
    sage: success, rho = M.verify_hyperbolicity(holonomy=True)
    sage: success
    True
    sage: trace = rho('aaB').trace(); trace # doctest: +NUMERIC9
    -0.1118628555? + 3.8536121048?*I
    sage: (trace - 2).contains_zero()
    False
    sage: (rho('aBAbaabAB').trace() - 2).contains_zero()
    True

Here, there is **provably** a fixed holonomy representation rho0 from
the fundamental group G of M to SL(2, C) so that for each element g of G
the matrix rho0(g) is contained in rho(g). In particular, the above
constitutes a proof that the word ‘aaB’ is non-trivial in G. In
contrast, the final computation is consistent with ‘aBAbaabAB’ being
trivial in G, but *does not prove this*.

A non-hyperbolic manifold (`False` indicates that the manifold might not
be hyperbolic but does **not** certify non-hyperbolicity. Sometimes,
hyperbolicity can only be verified after increasing the precision):

    sage: M = Manifold("4_1(1,0)")
    sage: M.verify_hyperbolicity()
    (False, [])

Under the hood, the function will call the `CertifiedShapesEngine` to
produce intervals certified to contain a solution to the rectangular
gluing equations. It then calls
`check_logarithmic_gluing_equations_and_positively_oriented_tets` to
verify that the logarithmic gluing equations are fulfilled and that all
tetrahedra are positively oriented.

volume(*accuracy=False*, *verified=False*, *bits_prec=None*)  
Returns the volume of the current solution to the hyperbolic gluing
equations; if the solution is sufficiently non-degenerate, this is the
sum of the volumes of the hyperbolic pieces in the geometric
decomposition of the manifold.

    >>> M = Manifold('m004')
    >>> M.volume()
    2.02988321
    >>> M.solution_type()
    'all tetrahedra positively oriented'

The return value has an extra attribute, accuracy, which is the number
of digits of accuracy as *estimated* by SnapPea. When printing the
volume, the result is rounded to 1 more than this number of digits.

    >>> vol, accuracy = M.volume(accuracy = True)
    >>> accuracy in (10, 63) # Low precision, High precision
    True

Inside SageMath, verified computation of the volume of a hyperbolic
manifold is also possible (this will verify first that the manifold is
indeed hyperbolic):

    sage: M.volume(verified=True, bits_prec=100)   #doctest: +NUMERIC24
    2.029883212819307250042405109?

# Census manifolds

Snappy comes with a large library of manifolds, which can be accessed
individually through the Manifold and Triangulation constructors but can
also be iterated through using the objects described on this page.

SnapPy’s iterators support several flexible methods for accessing
manifolds. They can be sliced (i.e. restricted to subranges) either by
index or by volume. Calling the iterator with keyword arguments such as
num_tets=1, betti=2 or num_cusps=3 returns an iterator which is filtered
by the specified conditions. In addition these iterators can determine
whether they contain a given manifold. They support python’s “A in B”
syntax, and also provide an identify method which will return a copy of
the census manifold which is isometric to the manifold passed as an
argument.

snappy.OrientableCuspedCensus* = OrientableCuspedCensus without filters*  
Iterator for all orientable cusped hyperbolic manifolds that can be
triangulated with at most 10 ideal tetrahedra. See
[\[Li\]](https://arXiv.org/abs/2512.02142) for background on these
manifolds.

    >>> for M in OrientableCuspedCensus[3:6]: print(M, M.volume())
    ...
    m007(0,0) 2.56897060
    m009(0,0) 2.66674478
    m010(0,0) 2.66674478
    >>> for M in OrientableCuspedCensus[-9:-6]: print(M, M.volume())
    ...
    o10_150721(0,0)(0,0)(0,0) 10.1494160640965
    o10_150722(0,0)(0,0)(0,0) 10.1494160640965
    o10_150723(0,0)(0,0) 10.1494160640965
    >>> for M in OrientableCuspedCensus[4.10:4.11]: print(M, M.volume())
    ...
    m217(0,0) 4.10795310
    m218(0,0) 4.10942659
    >>> for M in OrientableCuspedCensus(num_cusps=2)[:3]:
    ...   print(M, M.volume(), M.num_cusps())
    ...
    m125(0,0)(0,0) 3.66386238 2
    m129(0,0)(0,0) 3.66386238 2
    m202(0,0)(0,0) 4.05976643 2
    >>> M = Manifold('m129')
    >>> M in LinkExteriors
    True
    >>> LinkExteriors.identify(M)
    5^2_1(0,0)(0,0)

&nbsp;

snappy.OrientableClosedCensus* = OrientableClosedCensus without filters*  
Iterator for 11,031 closed hyperbolic manifolds from the census by
Hodgson and Weeks.

    >>> len(OrientableClosedCensus)
    11031
    >>> len(OrientableClosedCensus(betti=2))
    1
    >>> for M in OrientableClosedCensus(betti=2):
    ...   print(M, M.homology())
    ...
    v1539(5,1) Z + Z

&nbsp;

snappy.CensusKnots* = CensusKnots without filters*  
Iterator for all of the knot exteriors in the SnapPea Census, as
tabulated by Callahan, Dean, Weeks, Champanerkar, Kofman, Patterson,
Dunfield, and Li. These are the knot exteriors which can be triangulated
by at most 10 ideal tetrahedra. See
[\[Li\]](https://arXiv.org/abs/2512.02142) for more.

    >>> for M in CensusKnots[3.4:3.5]:
    ...   print(M, M.volume(), LinkExteriors.identify(M))
    ...
    K4_3(0,0) 3.47424776 False
    K5_1(0,0) 3.41791484 False
    K5_2(0,0) 3.42720525 8_1(0,0)
    K5_3(0,0) 3.48666015 9_2(0,0)

    >>> len(CensusKnots)
    3116
    >>> CensusKnots[-1].num_tetrahedra()
    10

&nbsp;

snappy.LinkExteriors* = LinkExteriors without filters*  
Iterator for all knots with at most 11 crossings and links with at most
10 crossings, using the Rolfsen notation. The triangulations were
computed by Joe Christy.

    >>> for K in LinkExteriors(num_cusps=3)[-3:]:
    ...   print(K, K.volume())
    ...
    10^3_72(0,0)(0,0)(0,0) 14.35768903
    10^3_73(0,0)(0,0)(0,0) 15.86374431
    10^3_74(0,0)(0,0)(0,0) 15.55091438
    >>> M = Manifold('8_4')
    >>> OrientableCuspedCensus.identify(M)
    s862(0,0)

By default, the ‘identify’ returns the first isometric manifold it
finds; if the optional ‘extends_to_link’ flag is set, it insists that
meridians are taken to meridians.

    >>> M = Manifold('7^2_8')
    >>> LinkExteriors.identify(M)
    5^2_1(0,0)(0,0)
    >>> LinkExteriors.identify(M, extends_to_link=True)
    7^2_8(0,0)(0,0)

&nbsp;

snappy.HTLinkExteriors* = HTLinkExteriors without filters*  
Iterator for all knots up to 14 or 15 crossings (see below for which)
and links up to 14 crossings as tabulated by Jim Hoste and Morwen
Thistlethwaite. In addition to the filter arguments supported by all
ManifoldTables, this iterator provides alternating=\<True/False\>;
knots_vs_links=\<’knots’/’links’\>; and crossings=N. These allow
iterations only through alternating or non-alternating links with 1 or
more than 1 component and a specified crossing number.

    >>> HTLinkExteriors.identify(LinkExteriors['8_20'])
    K8n1(0,0)
    >>> Mylist = HTLinkExteriors(alternating=False,knots_vs_links='links')[8.5:8.7]
    >>> len(Mylist)
    8
    >>> for L in Mylist:
    ...   print( L.name(), L.num_cusps(), L.volume() )
    ...
    L11n138 2 8.66421454
    L12n1097 2 8.51918360
    L14n13364 2 8.69338342
    L14n13513 2 8.58439465
    L14n15042 2 8.66421454
    L14n24425 2 8.60676092
    L14n24777 2 8.53123093
    L14n26042 2 8.64333782
    >>> for L in Mylist:
    ...   print( L.name(), L.DT_code() )
    ...
    L11n138 [(8, -10, -12), (6, -16, -18, -22, -20, -2, -4, -14)]
    L12n1097 [(10, 12, -14, -18), (22, 2, -20, 24, -6, -8, 4, 16)]
    L14n13364 [(8, -10, 12), (6, -18, 20, -22, -26, -24, 2, -4, -28, -16, -14)]
    L14n13513 [(8, -10, 12), (6, -20, 18, -26, -24, -4, 2, -28, -16, -14, -22)]
    L14n15042 [(8, -10, 14), (12, -16, 18, -22, 24, 2, 26, 28, 6, -4, 20)]
    L14n24425 [(10, -12, 14, -16), (-18, 26, -24, 22, -20, -28, -6, 4, -2, 8)]
    L14n24777 [(10, 12, -14, -18), (2, 28, -22, 24, -6, 26, -8, 4, 16, 20)]
    L14n26042 [(10, 12, 14, -20), (8, 2, 28, -22, -24, -26, -6, -16, -18, 4)]

SnapPy comes with one of two versions of HTLinkExteriors. The smaller
original one provides knots and links up to 14 crossings; the larger
adds to that the knots (but not links) with 15 crossings. You can
determine which you have by whether

    >>> len(HTLinkExteriors(crossings=15))

gives 0 or 253293. To upgrade to the larger database, install the Python
module ‘snappy_15_knots’ as discussed on the ‘installing SnapPy’
webpage.

&nbsp;

snappy.RibbonLinks* = RibbonLinks without filters*  
The database of ribbon links from Section 2.5 of [\[Dunfield and
Gong\]](https://arXiv.org/abs/2512.21825). Each link includes a
certificate describing the ribbon disks:

    >>> len(RibbonLinks(cusps=2))
    12143
    >>> M = RibbonLinks[1000]
    >>> M.name(), M.num_cusps(), M.volume()
    ('ribbon_2_16_3079d007', 2, 22.9002274714046)

The bands used show each link is ribbon are included. For this link, we
used 3 bands:

    >>> N = RibbonLinks['ribbon_2_23_f9c7aff2']
    >>> N.ribbon_cert[1::2]
    ['0d1c54_1_0', '5e5709_1_0', '144f625e5d29_5_2']

&nbsp;

snappy.NonorientableCuspedCensus* = NonorientableCuspedCensus without filters*  
Iterator for all nonorientable cusped hyperbolic manifolds that can be
triangulated with at most 5 ideal tetrahedra.

    >>> for M in NonorientableCuspedCensus(betti=2)[:3]:
    ...   print(M, M.homology())
    ...
    m124(0,0)(0,0)(0,0) Z/2 + Z + Z
    m128(0,0)(0,0) Z + Z
    m131(0,0) Z + Z

&nbsp;

snappy.NonorientableClosedCensus* = NonorientableClosedCensus without filters*  
Iterator for 17 nonorientable closed hyperbolic manifolds from the
census by Hodgson and Weeks.

    >>> for M in NonorientableClosedCensus[:3]: print(M, M.volume())
    ...
    m018(1,0) 2.02988321
    m177(1,0) 2.56897060
    m153(1,0) 2.66674478

There are also:

- Censuses of Platonic manifolds

As instances of subclasses of ManifoldTable, the objects above support
the following methods.

*class *snappy.database.ManifoldTable(*table=''*, *db_path=None*, *mfld_hash=\<function mfld_hash\>*, *\*\*filter_args*)  
Iterator for cusped manifolds in an sqlite3 table of manifolds.

Initialize with the table name. The table schema is required to include
a text field called ‘name’ and a text field called ‘triangulation’. The
text holds the result of M.triangulation_isosig(),
M.triangulation_isosig(decorated = True), or M.\_to_string().

Both mapping from the manifold name, and lookup by index are supported.
Slicing can be done either by numerical index or by volume.

The \_\_contains\_\_ method is supported, so M in T returns True if M is
isometric to a manifold in the table T. The method T.identify(M) will
return the matching manifold from the table.

find(*where=None*, *order_by='id'*, *limit=None*, *offset=None*)  
Return a list of up to limit manifolds stored in this table, satisfying
the where clause, and ordered by the order_by clause. If limit is None,
all matching manifolds are returned. If the offset parameter is set, the
first offset matches are skipped.

identify(*mfld*, *extends_to_link=False*)  
Look for a manifold in this table which is isometric to the argument.

Return the matching manifold, if there is one which SnapPea declares to
be isometric.

Return False if no manifold in the table has the same hash.

Return None in all other cases (for now).

If the flag “extends_to_link” is True, requires that the isometry sends
meridians to meridians. If the input manifold is closed this will result
in no matches being returned.

keys()  
Return the list of column names for this manifold table.

siblings(*mfld*)  
Return all manifolds in the census which have the same hash value.

Because of the large size of their datasets, the classes below can only
iterate through slices by index, and do not provide the identification
methods.

*class *snappy.AlternatingKnotExteriors(*indices=(0, 491327, 1)*)  
Iterator/Sequence for Alternating knot exteriors from the
Hoste-Thistlethwaite tables. Goes through 16 crossings.

&nbsp;

*class *snappy.NonalternatingKnotExteriors(*indices=(0, 1210608, 1)*)  
Iterator/Sequence for nonAlternating knot exteriors from the
Hoste-Thistlethwaite tables. Goes through 16 crossings.

# Verified computations

## Introduction

Several SnapPy methods use numerical computations with floating point
approximations and can potentially result in incorrect results. This
even applies to methods whose output is purely combinatorial such as
`canonical_retriangulation()`.

Many of these SnapPy methods can be supplied with a `verified` flag to
ensure that the result is provably correct. Note that verified
computations are only available when using SnapPy inside
SageMath. If the flag `verified=True` is
specified, an incorrect result is never returned. Instead the method
clearly indicates a failure, usually through an exception:

    sage: M=Manifold("m004")
    sage: M.drill_word('abc', verified=True, bits_prec = 40)
    ...
    InsufficientPrecisionError: When re-tracing the geodesic, the intersection with the next tetrahedron face was too close to the previous to tell them apart. Increasing the precision will probably avoid this problem.

Often, such a failure can be advoided by increasing the precision. In
particular, this applies if the exception is a (subclass of)
`InsufficientPrecisionError`:

    sage: M.drill_word('abc', verified=True, bits_prec = 60)
    m004_drilled(0,0)(0,0)

Note that,
`verify_hyperbolicity()`
is different though and does not throw an exception. Instead, it returns
a bool indicating success as part of its output. This is for
compatibility with
HIKMOT’s
`verify_hyperbolicty`:

    sage: M.verify_hyperbolicity(bits_prec=10)
    (False, [])
    sage: M.verify_hyperbolicity()
    (True,
     [0.50000000000000? + 0.86602540378444?*I,
      0.50000000000000? + 0.86602540378444?*I])

As illustrated above, the result consists of intervals (of type
SageMath’s `RealIntervalField` or `ComplexIntervalField`) if the output
of a computation is numerical and `verified=True` is specified. These
intervals contain the true value.

## Overview

Some examples of verified computations are:

- Verify the hyperbolicity of an orientable 3-manifold giving complex
  intervals for the shapes corresponding to a hyperbolic structure or
  holonomy representation with
  `verify_hyperbolicity()`:

      sage: M = Manifold("m015")
      sage: M.verify_hyperbolicity()
      (True,
       [0.6623589786224? + 0.5622795120623?*I,
        0.6623589786224? + 0.5622795120623?*I,
        0.6623589786224? + 0.5622795120623?*I])
      sage: M.verify_hyperbolicity(holonomy=True)[1].SL2C('a')
      [-0.324717957? - 1.124559024?*I -0.704807293? + 0.398888830?*I]
      [ 1.409614585? - 0.797777659?*I       -1.000000000? + 0.?e-9*I]

- Intervals for the volume and complex volume of a hyperbolic orientable
  3-manifold:

      sage: M = Manifold("m003(-3,1)")
      sage: M.volume(verified=True, bits_prec = 100)
      0.942707362776927720921299603?
      sage: M = Manifold("m015")
      sage: M.complex_volume(verified_modulo_2_torsion=True)
      2.8281220883? + 1.9106738240?*I

  (Note that when using verified computation, the Chern-Simons invariant
  is only computed modulo pi^2/2 even though it is defined modulo pi^2.)

- Give the (a close relative to the canonical cell decomposition) of a
  cusped hyperbolic manifold using intervals or exact arithmetic if
  necessary with
  `canonical_retriangulation()`:

      sage: M = Manifold("m412")
      sage: K = M.canonical_retriangulation(verified = True)
      sage: len(K.isomorphisms_to(K)) # Certified size of isometry group
      8

  **Remark:** For the case of non-tetrahedral canonical cell, exact
  values are used which are found using the
  LLL-algorithm
  and then verified using exact computations. These computations can be
  slow. A massive speed-up was achieved by recent improvements so that
  the computation of the isometry signature of any manifold in
  `OrientableCuspedCensus` takes at most a couple of seconds, typically,
  far less. Manifolds with more simplices might require setting a higher
  value for `exact_bits_prec_and_degrees`.

- The isometry signature which is a complete invariant of the isometry
  type of a cusped hyperbolic manifold (i.e., two manifolds are
  isometric if and only if they have the same isometry signature):

      sage: M = Manifold("m412")
      sage: M.isometry_signature(verified = True)
      'mvvLALQQQhfghjjlilkjklaaaaaffffffff'

  The isometry signature can be strengthened to include the peripheral
  curves such that it is a complete invariant of a hyperbolic link:

      sage: M = Manifold("L5a1")
      sage: M.isometry_signature(of_link = True, verified = True)
      'eLPkbdcddhgggb_baCbbaCb'

  See
  `isometry_signature()`
  for details.

  **Remark:** The isometry signature is based on the canonical
  retriangulation so the same warning applies.

- The maximal cusp area matrix which characterizes the configuration
  space of disjoint cusp neighborhoods with
  `cusp_area_matrix()`:

      sage: M=Manifold("m203")
      sage: M.cusp_area_matrix(method='maximal', verified=True)
      [   27.000000? 9.0000000000?]
      [9.0000000000?   27.0000000?]

  In this example, the cusp neighborhood about cusp 0 or 1 is only
  embedded if and only if its area is less than sqrt(27). The cusp
  neighborhood about cusp 0 is only disjoint from the one about cusp 1
  if and only if the product of their areas is less than 9.

- Compute areas for disjoint cusp neighborhoods with
  `cusp_areas()`:

      sage: M=Manifold("m203")
      sage: M.cusp_areas(policy = 'unbiased', method='maximal', verified = True)
      [3.00000000000?, 3.00000000000?]

  With the above parameters, the result is intrinsic to the hyperbolic
  manifold with labeled cusped.

- Find all slopes of length less or equal to 6 when measured on the
  boundary of disjoint cusp neighborhoods:

      sage: M=Manifold("m203")
      sage: M.short_slopes(policy = 'unbiased', method='maximal', verified = True)
      [[(1, 0), ...,  (1, 2)], [(1, 0), ...,  (1, 2)]]

  First block has all short slopes for first cusp, …, see
  `short_slopes()`
  for details.

  By Agol’s and
  Lackenby’s 6-Theorem any
  Dehn-filling resulting in a non-hyperbolic manifold must contain one
  of the above slopes. Thus,
  `short_slopes()`
  can be used to implement the techniques to find exceptional Dehn
  surgeries (arXiv:1109.0903 and
  arXiv:1310.3472).

- An example of finding all geodesics up to length 1:

      sage: from snappy.sage_helper import RIF
      sage: L = RIF(1)
      sage: M = Manifold("m003")
      sage: spec = M.length_spectrum_alt_gen(verified=True)
      sage: n = 0
      sage: for g in spec:
      ...       if g.length.real() > L:
      ...           break # Done! All subsequent geodesics will be longer.
      ...       if g.length.real() < L:
      ...           n += 1
      ...           continue
      ...       raise Exception("Interval too large. Increase precision.")
      sage: n
      4

Additionally, we can compute complex intervals for the shapes that are
guaranteed to contain a true solution to the rectangular gluing
equations that is not necessarily a geometric solution (specify
`bits_prec` or `dec_prec` for higher precision intervals.):

    sage: M = Manifold("m015(3,1)")
    sage: M.tetrahedra_shapes('rect', intervals=True)
    [0.625222762246? + 3.177940133813?*I,
     -0.0075523593782? + 0.5131157955971?*I,
     0.6515818912107? - 0.1955023488930?*I]

This is all based on a reimplementation of
HIKMOT which
pioneered the use of interval methods for hyperbolic manifolds (also see
Zgliczynski’s
notes). It can be
used in a way very similar to HIKMOT, but uses Sage’s complex interval
types for certification. It furthermore makes use of code by Dunfield,
Hoffman, Licata.

This verification code was contributed by Matthias Goerner.

## Verified computation topics

- Internals of verified computations
