<!-- Vendored from https://cgm.cs.mcgill.ca/~avis/C/lrslib/USERGUIDE.html (lrslib User Guide, version 7.3, matching installed lrslib 7.3a), converted to markdown; installation, mplrs, arithmetic-package, and lrsnash sections omitted -->

  

###   David Avis          avis@cs.mcgill.ca     [http://cgm.cs.mcgill.ca/~avis](http://cgm.cs.mcgill.ca/%7Eavis)

[What's new](./whatsnew.html)  

[Introduction](#Introduction)

[lrs: installation and usage](#Installation%20Section)

[mplrs: installation and usage](#mplrs)

[lrsnash: installation and usage  
](#nash)

   

[File formats](#file)

[Basic options](#Options)

[Arithmetic packages ](#Arithmetic%20Packages)

[Estimation](#Estimation)

  

[Extreme point enumeration and eliminating redundant
inequalities](#redund) [](#fourier)  

[Linear programming](#Linear%20Programming)

[Fourier elimination](#fourier)

[(New)Testing redundancy in projections](#hpred)

[Volume and triangulation](#Volume%20Computation)

[Voronoi Diagrams and Delaunay Triangulations  
  
](#Voronoi%20Diagrams)

[Linearities](#Linearities)

[Timing, interrupts and restarts  
](#timing)

[(New)Vertex/Facet cross reference listing  
](#hvref)

[Error messages and troubleshooting](#Timing%20and%20Interrupts)

[Hints and comments](#Hints%20and%20Comments)

[Acknowledgements and References](#Acknowledgements)

------------------------------------------------------------------------

------------------------------------------------------------------------

###  Introduction

A polyhedron can be described by a list of inequalities
(*H-representation)* or as by a list of its vertices and extreme rays
(*V-representation).lrs* is a C program that converts a H-representation
of a polyhedron to its V-representation, and vice versa.  These problems
are known respectively at the *vertex enumeration(VE)* and *convex
hull(CH) problems*.  
Fukuda's [FAQ page](https://people.inf.ethz.ch/fukudak/soft/soft.html)  
contains a more detailed introduction to the problem, along with many
useful tips for the new user.

*lrs* is based on the *reverse search* algorithm developed with Komei
Fukuda, see
[(](http://cgm.cs.mcgill.ca/%7Eavis/doc/avis/AF92b.ps)[AF](http://cgm.cs.mcgill.ca/%7Eavis/doc/avis/AF92b.ps)[1992)](http://cgm.cs.mcgill.ca/%7Eavis/doc/avis/AF92b.ps)
, modified to use lexicographic pivoting  and implemented in rational
arithmetic. It uses limited multithreading via OpenMP. 
[(](http://cgm.cs.mcgill.ca/%7Eavis/doc/avis/Av98a.ps)[Av](http://cgm.cs.mcgill.ca/%7Eavis/doc/avis/Av98a.ps)[1998a)](http://cgm.cs.mcgill.ca/%7Eavis/doc/avis/Av98a.ps)
contains a technical description, and
[(](http://cgm.cs.mcgill.ca/%7Eavis/doc/avis/Av98b.ps)[Av](http://cgm.cs.mcgill.ca/%7Eavis/doc/avis/Av98b.ps)[1998b)](http://cgm.cs.mcgill.ca/%7Eavis/doc/avis/Av98b.ps)
contains some computational experience.  
*mplrs* is a full parallel version of *lrs* based on Open MPI for
distributed systems, developed with Skip Jordan, see
[(AJ2015)](http://arxiv.org/abs/1511.06487).  

The input files are in *Polyhedra format* , developed with Fukuda. The
format is essentially self-dual, and the output file produced can be
read in as an input file, with very minor modifications, to perform the
reverse transformation. This format is compatible with that  used in
Fukuda's *[cddlib ](https://www.inf.ethz.ch/personal/fukudak/cdd_home/)*
package, which performs the same transformations using a version of the
*double description method*.  The program
[normaliz](https://www.normaliz.uni-osnabrueck.de/) provides a parallel
version of the double description method. Another program using the same
file format is the primal-dual method
*[pd](http://www.cs.unb.ca/profs/bremner/pd/),* developed by Bremner,
Fukuda and Marzetta .  It is essentially dual to *lrs,* and is very
efficient for computing H-representations of simple polyhedra, and
V-representations of simplicial polyhedra. It will compute the volume of
a polytope given by an H-representation. Links to additional VE/CH
programs are given
[here](http://cgm.cs.mcgill.ca/%7Eavis/C/lrslib/links.html).  

Polyhedra handled by *lrs * need not be full dimensional  and may
contain input linearities and redundant columns .  *lrs* accepts either
integer or rational input, and produces integer or rational output. All
computations are done exactly using hybrid arithmetic, starting with 64
bits and moving to 128 bits and extended precision (GMP or built-in) if
necessary, see [(AJ2021)](https://arxiv.org/abs/2101.12425).  Since it
is a pivot based method, *lrs* can be very slow for degenerate inputs:
i.e. H-representations of non-simple polyhedra, and V-representations of
non-simplicial polyhedra. On the other hand, it does not store the
vertices/ rays or facets produced, so for very large problems it may be
the only method that can solve the problem.  Using mplrs, even with just
a few cores, significantly speeds up the computation. A discussion of
various vertex enumeration/convex hull methods and the types of
polyhedra that cause them to behave badly is contained in [(ABS
1997).](http://cgm.cs.mcgill.ca/%7Eavis/doc/avis/ABS96a.ps)  A more
recent discussion with extensive empiral tests can be found in
[(AJ2017)](https://arxiv.org/abs/1511.06487).  Considerable technical
assistance over several decades has been provided by David Bremner.  

 Functions of *mplrs*/*lrs* include:

- [V-H transformation](#Installation%20Section): converting an
  H-representation to a V-representation and vice versa  
- [Estimating](#Estimation) the number of vertices/rays or facets of a
  polytope, and estimating the total running time (lrs only)  
- [Triangulating and computing the volume](#Volume%20Computation) of a
  polytope given by a V-representation
- Removing [redundancy](#redund) from an H or V-representation and
  computing a [minimum representation](#redund). Parallel version in
  mplrs (v7.3 new)
- [Projecting](#fourier) a polyhedron to a subset of its variables
  (Fourier elimination). Parallel version in mplrs (v7.3 new)
- Determining if an inequality is [redundant in computing the
  projection](#hpred) to a subset of its variables (uses SMT-solver,
  v7.2 new)  
- Solving [linear programming](#Linear%20Programming) problems in exact
  arithmetic (Simplex method, lrs only)  
- Computing the [Voronoi](#Voronoi%20Diagrams) vertices and rays for an
  input set of data points and the corresponding [Delaunay
  triangulation](#Voronoi%20Diagrams)  
- [Eliminating](#eliminate) variables in linearities in
  H-representations and [extracting columns](#eliminate) from
  V-representations (lrs only)
- Computing all [Nash equilibria](#nash) for 2-person matrix games
  (lrsnash)
- Computing a [cross reference table](#hvref) of vertices/rays vs
  facets  
- The ability to [suspend and restart](#timing) execution at any time
  for H-V transformations  

Redundancy removal involves the removal of any inequalities that are not
required to represent the polyhedron in an H-representation. For a
V-representation it is  the problem of evaluating the extreme points and
extreme rays. Finding a minimum representation involves locating any
hidden linearities in the input file. These problems are normally 
considerably easier than the H to V and V to H transforamtions performed
as they are performed by linear programming. In some cases, redundancy
can greatly slow the processing time taken for H-V transformation using
*lrs/mplrs,* and it is advisable to remove any redundancy and hidden
linearities from the input file before starting a long run.  

These programs can be distributed freely under the GNU GENERAL PUBLIC
LICENSE. Please read the file COPYING carefully before using.  Please
inform the authors of any interesting applications for which these
programs were helpful.

------------------------------------------------------------------------

lrslib installation and usage  

Package install is the simplest for linux or WSL/linux users, but may
not contain the latest version of lrslib:

Debian/Ubuntu (2025.3.25: v7.1):  sudo apt install lrslib    
(maintained by David Bremner \<bremner at debian.org\> )

Fedora (2025.3.25: v7.3):              sudo dnf install lrslib    
(maintained by Jerry James \<loganjerry at gmail.com\> )  

Additional instructions for installing **mplrs**, a multithreaded
implementation of **lrs** using MPI, are [here](#mplrs).  

Precompiled binaries lrs, lrsgmp for some Linux, Apple and Windows
machines are
[here](https://cgm.cs.mcgill.ca/%7Eavis/C/lrslib/archive/binaries/).  
These may be slower for problems requiring very long integers.  

Install from source code:

- From lrs home page, click on "Download" and retrieve the file
  lrslib-073.tar.gz
- Unpack with:
- Go to the new directory
-  make lrs with various arithmetic packages (it may be necessary to
  edit makefile to set the path to the gmp library)

        This produces binaries **lrs** (hybrid arithmetic) and the
usually slower  **lrsgmp** (GMP arithmetic)  

         For compilers without \_\_int128 and/or OpenMP support you will
need to edit the makefile as indicated at the beginning of that file.  
  

- You will need to have write permission to /tmp to run the hybrid
  arithmetic programs lrs. Temporary files are normally removed before
  termination.  
    
- If  you do not have GNU MP installed you can try using the built in
  lrs [arithmetic package](#Arithmetic%20Packages):  
- Test the program 

This is a list of the 8 vertices with each co-ordinate +/- 1.  The
\*\*\*\*\* should be replaced by the actual number, 8, of vertices.
Since *lrs* does not save the output produced, it does not know this
value until the execution terminates. This output is now essentially the
same as file cube.ext. To complete the test type:  

Now the output produced is essentially the file cube.ine, with the
inequalities appearing in a different order.  
  

Binaries produced by % make lrs or % make lrsgmp  

            **lrs**                 hybrid [arithmetic
package](http://cgm.cs.mcgill.ca/%7Eavis/C/lrslib/USERGUIDE63.html#Arithmetic%20Packages)
starting with  64 bit arithmetic, then 128 bit, then GMP.  
            **lrsgmp**        GMP arithmetic only  
             
           
  
Additional instructions for installing **mplrs**, a multithreaded
implementation of **lrs** using MPI, are [here](#mplrs).  

###  File formats

&nbsp;

**Note for cdd users**: *lrs* uses essentially the same file format as
*cdd*. Files prepared for *cdd* should work with little or no
modification. Note that  the V-representation corresponds to the "hull"
option in *cdd*. Options specific to *cdd* can be left in the input
files and will be ignored by *lrs*.  Note the input files for *lrs* are
read in free format, after the line **m n rational** *lrs* will look for
exactly m\*n rationals or integers separated by white space (blank, 
carriage return, tab etc.). *lrs* will not "drop" extra columns of input
if n is less than the number of columns supplied.  

------------------------------------------------------------------------

###  Basic options    Also see:     [Online manual](http://cgm.cs.mcgill.ca/%7Eavis/C/lrslib/man)

**allbases**

**bound  x                           **         // Use with
H-representation  - for lrs or nash //  

Either the maximize or minimize option should be selected. x is an
integer or rational.  
For maximization (resp. minimization) the reverse search tree is
truncated  whenever the current objective value is less (resp. more)
than x .  

  
**cache n**

**debug  startingbasis endingbasis**

> Print out cryptic but detailed trace, dictionaries etc. starting at
> \#B=startingbasis and ending at \#B=endingbasis. **debug 0 0** gives a
> complete trace.

**digits n    **            // placed before the begin statement//

**dualperturb  
**

If lrs is executed with the maximize or minimize option, the reverse
search tree is rooted at an optimum vertex for this function.  
If there are mulitiple optimum vertices, the output will often not be
complete. This option gives a small perturbation to the objective to
avoid this.  
A warning message is given if the starting dictionary is dual
degenerate**.**  

  
**eliminate** **k   i₁ i₂ ...
i_(k) **   **                                              new in v7.2  
**

   (H-representation) Eliminates k variables in an H-representation
corresponding to cols **i₁ i₂ i ... i_(k )** by projection onto the  
  remaining variables using the Fourier-Motzkin method.  Variables are
eliminated in the order given and redundancy is removed  
  after each iteration.  
  (V-representation) Delete the k given columns from the input matrix
and remove redundancies (cf. extract where redundancies  
  are not removed).  
  Column indices are between 1 and n-1 and column zero cannot be
eliminated.  The output is a valid lrs input file.   
  See [Fourier
elimination](file:///C:/Users/avis/Desktop/User%27s%20Guide%20for%20lrs.html#fourier),
also **project** and **extract  
  
**  
**estimates k**     Estimate the output size. Used in conjunction with
maxdepth - see
[Estimation.](file:///C:/Users/avis/Desktop/User%27s%20Guide%20for%20lrs.html#Estimation)

&nbsp;

**extract k   i₁ i₂ ... i_(k          )** (lrs only)  v7.2**  
      ** (H-representation) A preprocessing step to remove linearities
(if any) in an H-representation and resize the A matrix.  The  
       output as a valid lrs input file. The resulting file will not
contain any equations but may not be full dimensional as there  
       may be additional linearities in the remaining inequalities.
Options in the input file are stripped.  The user can specify  
       the **k** columns  **i₁ i₂ ... i_(k)** to retain otherwise if k=0
the columns are considered in the order 1,2,..n-1.  Linear dependent  
       columns are skipped and additional indices are taken from
1,2,...,n-1 as necessary.  If there are no linearities in the input  
       file the given columns are retained and the other ones are
deleted.  
       (V-representation) Extract the given columns from the input file
outputing a valid lrs input file.  Options are stripped.**  
      ** (See also **eliminate** and **project**)**  
  
geometric  **               // H-representation  or voronoi option only
//

          For more information and an example see Geometric Rays in
[Hints and Comments](#Hints%20and%20Comments) .  
  
**incidence**  
           This option automatically switches on **printcobasis** , so
see below for a description of this option first.  

> Can be used with printcobasis n. (Ver 4.2b)
>
> For input H-representation, indices of all input inequalities that
> contain the vertex/ray that is about to be output. For a simplicial
> face, there is no new output, since these indices are already listed.
> Otherwise, the additional tight inequalities are listed after a colon.
> Eg:  
> **V#1 R#0 B#1 h=0 facets  12 14 15 16 : 9 10 11 13 I#8 det= 8**  
> ** 1  0  0  0  1**  
> The vertex **0 0 0 1** satisfies 8 input inequalities as equations, as
> indicated by **I#8** : those with indices **12,14,15,16** are in the
> cobasis, and those with indices **9, 10, 11, 13** are in the basis.
> For a ray:  
> **V#1 R#5 B#1 h=0 facets  5 9\* 10 11 12 13 : 2 3 4 I#8 det= 8**  
> ** 0  1  1  0  0  1  1**  
> Here the ray **1  1  0  0  1  1** lies on 8 inequalities, with indices
> **5 10 11 12 13** in basis and **2 3 4 i**n cobasis. The starred index
> **9\*** indicates that the ray is terminated by the input inequality
> 9. This inequality is in the cobasis and defines the vertex from which
> the ray starts.
>
> For input V-representation, indices of all input vertices/rays that
> lie on the facet that is about to be output:  
> **F#5 B#3 h=2 vertices/rays  7 8\* 11 13 15 : 1 3 5 9 I#8 det= 16**  
> **1 -1  0  0  0**  
> The facet generated by inequality x₁ \<= 1 contains 8 input vertices,
> as indicated by I#8: those with indices **7,11,13,15** are in the
> cobasis, and those with indices **1 3 5 9** are in the basis.The
> starred index **8\*** indicates that this vertex  is also in the
> cobasis, but is not contained in the facet. It arises due to the
> lifting operation used with input V-representations.

**\#incidence**

> The same as printcobasis. Included for compatability with *cdd.*

**linearity  k  i₁ i₂ i ... i_(k)**

> The input contains k linearities in rows **i₁ i₂ i ... i_(k)** of the
> input file are equations. See [Linearities.](#Linearities)

**maxdepth k**

**maximize ** **a₀ a₁ ...
a_(n-1)** **                                          ** //
H-representation  only //  
**minimize  ** **a₀ a₁ ...
a_(n-1)**                                           // H-representation 
only //

If used with lrs the starting vertex maximizes (or minimizes) the
function  a₀ + a₁ x ₁ + ... + a_(n-1) x_(n-1).  
The dualperturb option may be needed to avoid dual degeneracy.  
See Nash Equilibria and  [Linear Programming](#Linear%20Programming)  

**maxcobases n        ** //from Version 6.0 //  
       After n cobases have been generated lrs terminates and returns
restart data for all unexplored roots of subtrees (except for leaves
which are output). These subtrees are the unexplored siblings on the
path back to the root of the reverse search tree. Used by
[mplrs](#mplrs) to break up large subtrees into smaller pieces.  
**  
maxincidence n  k         //from v.7.3//  
      ** Prunes the search tree when the depth is at least k and the
current vertex/facet has incidence at least n.   
       Using **verbose** a message is printed whenever the search tree
is pruned.**  
  
maxoutput n**     
       Limits number of output lines produced (either vertices+rays or
facets) to n  
**  
mindepth k**

**nonnegative                     ** // This option must come before the
begin statement//  
                                                                                           
//H-representation only //  
           Bug: Can only be used if the origin is a vertex of the
polyhedron 

> For problems where the input is an H-representation of the form
> b+Ax\>=0, x\>=0 (ie. all variables non-negative, all constraints
> inequalities) it is not necessary to give the non-negative constraints
> explicitly if the nonnegative option is used. This option cannot be
> used for V-representations, or with the linearity option (in which
> case the linearities will be treated as inequalities). This option may
> be used with redund , but the implied nonnegativity constraints are
> not tested themselves for redundancy. To test everything it is
> necessary to enter the nonnegativity constraints explicitly in the
> input file. (In Ver 4.1, the origin must be a vertex).  

**printcobasis  k                                 **

**printslack              **          // Use with H-representation //  
  

lrs prints a list of the indices of the input inequalities that are
satisfied strictly for the current vertex, ie. corresponding slack
variable is positive.  
If nonnegative is set, the list will also include indices n+i for each
decision variable x_(i) which is positive.  
  

  
**project** ****k   i₁ i₂ ...
i_(k)**                                                  new in v7.2  
**

       (H-representation) Project the polyhedron onto the **k**
variables corresponding to cols **i₁ i₂ ... i_(k)** using the
Fourier-Motzkin  
       method. Column  indices are between 1 and n-1 and column zero is
automatically retained.  Variables not contained in the list  
       are eliminated using a heuristic which chooses the column which
minimizes the product of the number of positive and negative  
       entries.  Redundancy is removed after each iteration using linear
programming.  
       (V-representation) Extract the k given columns from the input
matrix and remove redundancies. Column  indices are between 1  
       and n-1 and column zero is automatically extracted (cf. extract
where redundancies are not removed).  
       The output as a valid lrs input file.  See [Fourier
elimination](#fourier), also **eliminate** and **extract**  
  

**  
**  
****redund start end                      new in v7.1  
          **** Check input line numbers from **start** to **end** and
remove any redundant lines.  
            **redund 0 0**  will check all input lines.  See
[redund](http://cgm.cs.mcgill.ca/%7Eavis/C/lrslib/USERGUIDE71.html#redund)**  
  
redund_list k   i₁ i₂ ... i_(k                 )** ****new in v7.1****

Check the **k** input line numbers with indices **i₁ i₂ ... i_(k)** 
from and remove any redundant lines. See [redund](#redund)  
  

**restart  V# R# B# depth {facet \#s or vertex/ray \#s**}   
**\[integervertices n**\]                                              
                    /\* new in V 7.0 \*/             

&nbsp;

****startingcobasis i₁ i₂ i ... i_(n-1)**  
**

******testlin      (before the begin line only)   H-representation
only**  (new 7.3)**** ****  
**   **  

**threads  n**     (new in 7.3) lrs only  

**truncate                                           ** //
H-representation only //      

> The reverse search tree is truncated(pruned)  whenever a new vertex is
> encountered. Note: This does note necessarily produce the set of all
> vertices adjacent to the optimum vertex in the polyhedron, but just a
> subset of them. See
> [here](http://cgm.cs.mcgill.ca/%7Eavis/C/lrslib/lexpos.html) for a
> description of how to use this option.

**verbose**

> Print slightly more detailed information about the run.

**volume                                             ** //
V-representation  only //

**voronoi                                             ** //
V-representation  only - place immediately after end statement //

------------------------------------------------------------------------

###   Linear Programming             

**lponly**

             and one of the options maximize or minize:

**maximize a₀ a₁ ... a_(n-1)**                                          
// H-representation  only //

**minimize a₀ a₁ ...
a_(n-1)**                                             //
H-representation  only //

To print the dictionary at a few key points also include the option:

**verbose  
**

**New in V4.2.** Dual variables are now printed at termination. If the
linearity option is used, only a partial list of dual variables will be
given.  
                       Dual variable y_(i) refers to inequality number i
in the input.  

------------------------------------------------------------------------

###  Volume and triangulation 

*lrs* can be used to compute the volume of a full dimensional polytope
given as a V-representation. This follows from the fact that lex-postive
bases form a triangulation of the facets, and that a V-representation is
always lifted. See "Theoretical Description" on lrs home page for some
remarks on this. The option

**volume    **
                                                                       
// V-representation only //

will cause the volume to be computed. For input cube.ext, the output
is:  
**\*Volume=8**  

The triangulation can be output by adding also the option verbose.  
This would give the output:  

F#0 B#1 h=0 vertices/rays  4 6 7 8 I#8 det= 8   
 1  1  0  0   
 1  0  1  0   
 1  0  0  1   
F#3 B#2 h=1 vertices/rays  4 5 6 7 I#8 det= 8   
F#3 B#3 h=2 vertices/rays  3 4 5 7 I#8 det= 8   
 1 -1  0  0   
F#4 B#4 h=3 vertices/rays  2 3 4 5 I#8 det= 8   
 1  0  0 -1   
F#5 B#5 h=4 vertices/rays  1 2 3 5 I#8 det= 8   
F#5 B#6 h=2 vertices/rays  2 4 5 6 I#8 det= 8   
 1  0 -1  0   
end  
\*Sum of det(B)= 48   
\*Volume= 8   

Each of the 6 bases corresponds to a simplex.  
The first simplex is composed of vertices 4 6 7 8, second simplex is 4 5
6 7, etc.  

If the **volume** option is applied to an H-representation, the results
are not predictable. If the option is applied to a V-representation of
 a polytope that is not full dimensional, the volume of a projected
polytope is computed. The projection used is to the lexicographically
smallest coordinate subspace, see [Avis, Fukuda, Picozzi
(2002)](http://cgm.cs.mcgill.ca/%7Eavis/doc/avis/AFP02a.ps). 

For polytopes given by a H-representation, it will first be necessary to
compute the V-representation.  

------------------------------------------------------------------------

### Voronoi diagrams and Delaunay triangulations 

*lrs* can be used the compute the V-vertices of a Voronoi diagram of a
set of data points in n-1 dimensional space. To do this we use a
standard lifting procedure (see, e.g., Edelsbrunner, "Algorithms in
Combinatorial Geometry," pp 296-297) . Each point is mapped to a half
space tangent to the parabaloid in n dimensions, by the mapping:

p₁  , p₂  , ...., p _(n-1)     -\>    (p₁ ²  +   p₂² +  ...   + 
p_(n-1)²  ) - 2 p₁  x ₁  - 2 p₂  x₂ - .... - 2  p _(n-1) x_(n -1 ) + x
_(n)\>= 0

*lrs* is applied to the H-representation so created.  This
transformation is performed automatically for a V-representation if the

**voronoi         ** // V-representation only - place immediately after
end statement //

option is specified.  
**Note**: The input file must consist entirely of data points (no rays),
i.e.. there must be a one in column one of each line. The **volume**
option should not be used, since the volume reported will not be the
volume of the original V-representation.  
The output will consist of the Voronoi vertices (columns beginning with
a one) and Voronoi rays (columns beginning with zero) for the Voronoi
diagram defined on the data points.  If the **printcobasis** option is
given, the n "**data points**" indices produced will tell which set of
input data points corresponds to the given Voronoi vertex or ray. In
case of degeneracies, a given Voronoi vertex may be generated by more
than n of the input data points. In this case, use of the **allbases**
option will cause all  sets of n input data points corresponding to a
Voronoi vertex to be printed. Each cobasis will define a **Delaunay
triangle** in the dual. For Voronoi rays, the immediately preceding 
cobasis is the cobasis of the the Voronoi vertex from which the ray
emanates.  The index followed by a **\*** is the data point to drop in
order to generate the ray. If the **geometric** option is given the
correspondence between Voronoi rays and Voronoi vertices will be
produced automatically.

**Example:** Compute the Voronoi diagram and Delaunay triangulation of
the planar point set (0,0), (2,1), (1,2), (0,4), (4,0), (4,4) (2,-4).  

[TABLE]

  

  

[TABLE]

Visualizations made using [GeoGebra](https://www.geogebra.org).  

###   redund: extreme point enumeration and eliminating redundant inequalities     (new options parallel version from v7.1) 

###   minrep: finding a minimum representation of an H- or V-representation      (new options parallel version from v7.3) 

A convex hull problem that occurs frequently is to enumerate the extreme
points (vertices) of a given set of input points. This problem is in
fact much simpler than the problem of finding the facets of the given
input point set. It can be solved by linear programming.  The dual
problem is to remove redundant inequalities from an H-representation. An
input  inequality is redundant if it can be deleted without changing the
polyhedron. It is strongly redundant if it is not satisfied as strict
inequality by any feasible point. A vertex/ray in a V-representation is
strongly redundant if it is strictly interior to the convex hull.  
  
An H-representation may contain "hidden linearities" or inequalities
that are always satisfied as equations. A similar situation occurs in a
V-representation where the convex hull contains a line. The minimum
representation problem is to identify all linearities in an input file,
output them explicity using the linearity option, and then remove any
remaining redundant rows. The dimension of the input set is output at
the end of the computation.  
  
Redundancy removal can be obtained by using the lrs clone redund or by
lrs via the redund/redund_list options described above.  
  
A minimum representation can be obtained by using the lrs clone minrep
or by lrs via the testlin (before the begin line) and redund/redund_list
options.  
mplrs can compute a minimum representation in parallel by use of the
-minrep command line argument. Due to technical issues in the
parallelization mplrs does not do redundancy removal without also
computing a minimum representation.  
  
The ouput will be streamed if the verbose option is included after the
end line.  
On each line \*nr indicates non-redundant, \*re indicates redundant,
\*sr indicates strongly redundant, and \*li indicates linearity.  
  
**Usage:**  
(1) **With options**  (allows partial redundancy checking for large
inputs)  
  
Add the [redund](#redopt) or [redund_list](#redopt) option after the end
statement of a H- or V-representation.  
Execute **% lrs filename**  **or   %mpirun -np \<procs\> mplrs
filename**  
  
If more than one redund/redund_list option is in the input file the last
one read takes priority.  
  
(2) **Without options**  (complete redundancy check of all input lines,
overidden by redund/redund_list option in input)  

To remove input lines that are not vertices/rays from a V-representation
or redundant inequalities from an H-representation use the command:

For example, using the file mit.ine from the distribution:  
  
          % redund mit.ine  

> \*redund:lrslib v.7.1 2020.5.23(64bit,lrslong.h,overflow checking)  
>   
> \*Input taken from file mit.ine  
> mit.ine  
> \*mulint   : max(\|a\|,\|b\|) \> 2147483647  
>   
> \*redund2 found - restarting  
> \*redund:lrslib v.7.1 2020.5.23(128bit,lrslong.h,overflow checking)  
>   
> \*Input taken from file mit.ine  
> mit.ine  
> \*row 75 was redundant and removed  
> \*row 77 was redundant and removed  
> \*row 89 was redundant and removed  
> --------------------------  
> \*row 709 was redundant and removed  
> H-representation  
> begin  
> 708  9  rational  
>  36  0  0 -2 -2 -1  0  0  0  
> ----------------------------  
>    
>  0  0  0  0  0  0  0  0  1  
> end  
> \*Input had 729 rows and 9 columns: 21 row(s) redundant  
> \*Overflow checking on lrslong arithmetic  
> \*redund:lrslib v.7.1 2020.5.23(128bit,lrslong.h)  

From this output we first see that redund tried 64 bit arithmetic but
detected an overflow and reran with 128 bit arithmetic.  
It found 21 redundant rows which were removed from the file.  
The resulting output file can be used directly with lrs.  
In fact, lrs works best if the input is non-redundant, see the section
[Redundancy vs Degeneracy.](#Hints%20and%20Comments)

------------------------------------------------------------------------

### Linearities    

  
**linearity  k  i₁ i₂ i ... i_(k)**

> The input file contains k linearities. If the input is a
> H-representation, the rows **i₁ i₂ i ... i_(k)** of the input file are
> equations. For a V-representation, the rows with these indices should
> begin with zero in column one, and will be interpreted as lines rather
> than rays.  Linearities defined on the input vertices of a
> V-representation are not defined, but the program will accept them and
> produce some output. Each of the indice **i_(k)** must be a distinct
> number between **1** and **m**. With an  H-representation, linearities
> are useful for enumeration of vertices on a facet or lower dimensional
> subspace. For example the file:
>
> **cube_ridge**  
> **\*cube of side 2 centred at the origin**  
> **H-representation**  
> **linearity 2  1 5**  
> **begin**  
> **6 4 rational**  
> **1 1 0 0**  
> **1 0 1 0**  
> **1 0 0 1**  
> **1 -1 0 0**  
> **1 0 -1 0**  
> **1 0 0 -1**  
> **end**
>
> causes vertices to be enumerated on the ridge which is the
> intersection of the two facets
>
> x₁ = -1   and   x₂ = 1
>
> so the output is the pair of vertices
>
> cube_ridge  
> \*Input linearity in row(s) 1 5  
> V-representation  
> begin  
> 2  4  rational  
>  1 -1  1  1  
>  1 -1  1 -1  
> end
>
> Specifying linearities in this way will often produce
> [redundancy](#Hints%20and%20Comments) , especially if the dimension of
> the problem is reduced considerably. As a preprocessing step, it is
> useful to apply to remove any redundancy by [*redund*](#redund). In
> the case of the above problem the output produced by *redund* is:
>
> cube  
> \*Input linearity in row(s) 1 5  
> \*row 2 was redundant and removed  
> \*row 4 was redundant and removed  
> H-representation  
> linearity 2 1 2  
> begin  
> 4 4 rational  
>  1  1  0  0  
>  1  0 -1  0  
>  1  0  0  1  
>  1  0  0 -1
>
> and two redundant halfspaces were removed.
>
> Redundant columns are closely related to linearities. If we examine
> the V-representation of cube_ridge above we can see that it is just a
> line segment in 3 dimensional space. Further,  columns 2 and 3 are
> multiples of column 1. If lrs is applied to this file, the column
> redundancies give rise to two linearities, so the output will appear
> as the H-representation given above: geometrically the intersection of
> two planes (the linearities) with two half-planes (defining the
> endpoints of the line segment).
>
> In general, the representation of the linearity space is not unique,
> however the one produced by lrs should be the same as that produced by
> cdd.

  

------------------------------------------------------------------------

###  Error messages and troubleshooting

The most common error occurs from an incorrect input file specification,
please check the section [File Formats](#file) carefully. In particular,
*lrs* does not check the type or number of input coefficients
specified.  After the line  
**m n rational**  
you must specify **exactly** m\*n rational or integer coefficients. They
are read  in **free format** , but normally each input facet or
vertex/ray is begun on a new line.  See [note for cdd
users.](#Note%20for%20cdd%20users)

The following error messages are produced by *lrs* . They are  arranged
in alphabetic order.

**Cannot find linearity in the basis  
**

> The linearity option was specified but a basis cannot be created.
> Check the linearity indices are all less than n-1 and are disitinct.

**Data type must be integer of rational**

**Digits must be at most 2295  Change MAX_DIGITS and recompile     (This
message does not appear if the default gmp arithmetic package is used)**

**Invalid input: check you have entered enough data!  
**

> Usually means that end of file was reached before enough input data
> was read.  

**  
Invalid Co-basis - does not have correct rank**

**Maximize/minimize only valid for H-representation**

**No begin line**

**No data in file**

**No feasible solution**

**Starting cobasis indices must be distinct and in range 1 .. m**

**Trying to restart from infeasible dictionary**

**mplrs error messages**  
**  
Error: lponly option not supported - use lrs!**

**The following message may be produced when building lrs on macOS**  
  
**OpenMP support not found, disabling OpenMP parallel build  
**

  
  

------------------------------------------------------------------------

Hints and comments

####  H- vs V- representation

 *lrs* is programmed to manipulate H-representations directly. A file
presented as a V-representation is processed by lifting it to a cone in
one higher dimension, which is treated internally as a H-representation.
If the input file is a polytope which contains the origin, then the user
has two options. Submit it as a V-representation and have it processed
as just described, or submit it as a H-representation, and interpret the
output as a list of facet inequalities rather than "vertices". Since
this will not be lifted, it will be processed in a different way by
*lrs*. Sometimes a degenerate V-representation may run more quickly as a
H-representation, and sometimes more slowly. To decide which
representation to use for a large problem, the user can run the
**estimates** option and choose the representation with fewest estimated
bases.  
 

#### Redundancy vs Degeneracy

For an H-representation, an input is redundant if some inequality can be
deleted without changing the polyhedron. It is degenerate if (in d
dimensions) at least one vertex lies on d+1 or more facets.  Similarly
in a V-representation an input is redundant if some input point is not a
vertex of the convex hull.  It is degenerate if some facet contains d+1
or more input points. The [options](#Options)   **printcobasis** and
**incidence** give degeneracy information. Degeneracy causes pivot  or
triangulation based methods such as *lrs* to  run slowly. Redundancy is
one cause of degeneracy, but it can be avoided by pre-processing the
input files. See section [redund: extreme Point Enumeration and
Redundant Inequalities](#redund) for instructions on how to do this.
This pre-processing is unnecessary if it is known that the input is
non-redundant.

Even with redundant input removed a polyhedron may be highly degenerate.
In distribution directory ine/metric there are many highly degenerate
combinatorial polytopes. These are difficult problems for all vertex
enumeration/convex hull programs that use pivoting, such as *lrs*.  For
example, the file *cp6.ine* is a polytope with 368 facets in  16
dimensions. It has 32 vertices, but computing these required the
evaluation of 4,844,923,002 bases!(see [Avis-Jordan,
2017](https://arxiv.org/abs/1511.06487))  

#### Memory considerations

The strong point of *lrs* is that it does not save the output produced,
so in theory it cannot run out of memory.  With cache size one all
memory is allocated at the beginning, so if *lrs* starts running it will
not run out of memory. It is possible however that the number of digits
required to do the calculations exceeds the amount specified on the
**digits** option, or the default. In practice, this problem will also
arise early in the computation. In any case, a message is printed and
the calculation can be restarted. In order to improve performance, some
dictionaries should be cached. The default of 10 can be overridden by
the **cache**option. If the dictionary is in the cache it does not need
to be recomputed when backtracking, reducing  processing time by about
40%. Since the cache is allocated dynamically, a cache size that is too
large can potentially use up large ammounts of machine memory.

#### Geometric Rays

A minimum V-representation of a polyhedron is a minimum set of vertices
and rays such that each point in the polyhedron can be expressed as a
convex combination of vertices plus a non-negative combination of rays.
For the cube, if we delete the inequality  
x₃ \<= 1, i.e.. the line 1 0 0 -1 from file *cube.ine*, we get the
output:  
**V-representation**  
**\*\*\*\*\* 4 rational**  
**1 1 1 -1**  
**0 0 0 1**  
**1 -1 1 -1**  
**1 1 -1 -1**  
**1 -1 -1 -1**  
**end**  
indicating the polyhedron is the convex combination of 4 vertices and 1
ray. With the **geometric** option, we get the output:  
**V-representation**  
**begin**  
**\*\*\*\*\* 4 rational**  
**1 1 1 -1**  
**0 0 0 1  \* 1 1 1 -1**  
**1 -1 1 -1**  
**0 0 0 1  \* 1 -1 1 -1**  
**1 1 -1 -1**  
**0 0 0 1  \* 1 1 -1 -1**  
**1 -1 -1 -1**  
**0 0 0 1  \* 1 -1 -1 -1**  
**end**  
This indicates that geometrically, the polyhedron has 4 parallel extreme
rays (0,0,t) , one incident to each vertex. With the **geometric**
option, all rays will be printed. Without the option, *lrs* tries to
print each ray once, but in some cases duplicates will remain, see 
subsection Output Duplication.  
  
**Output Duplication**

For degenerate inputs, pivot based methods for vertex/ray enumeration
such as *lrs* may generate the same output ray many times. An output is
only printed when it occurs with a lexicographically minimum basis. This
removes all duplicate vertices, but rays may still be output more than
once. This is due to the fact that duplicate geometric rays cannot
always be detected without storing the output. Since V-representations
are automatically lifted to a higher dimension, this will not happen for
facet enumeration. Unless the **allbases** option is specified, *lrs*
makes checks in order to remove duplicates.   A warning message is
produced when duplicates may occur in the output. They can be removed
using the program *buffer.c*. Two important types of input never produce
duplicate output: polytopes (i.e. bounded polyhedra) and cones (i.e.
polyhedra where the origin is the only vertex).

------------------------------------------------------------------------

Acknowledgements and References

I would like to thank many people for helping with this implementation
project. Komei Fukuda encouraged me from the start, collaborated in
designing the file formats, and provided many suggestions for improving
the code. Debugging would have been almost impossible without the use of
his program cdd as a benchmark. David Bremner implemented memory
allocation, cacheing and signals. Ambros Marzetta demonstrated the
importance of cacheing and lrslong is based on his earlier
implementation of this as prs_single.  Jerry Quinn coded the integer
divide routine. Bug reports were provided by many users, for which I
thank them. In particular Gerardo Garbulsky's extensive use of earlier
versions suggested many refinements and Andreas Enge helped debug the
volume computation. Tallman Nkgau contributed fourier.  

D. Avis, lrs: A Revised Implementation of the Reverse Search Vertex
Enumeration Algorithm,
[http://cgm.cs.mcgill.ca/~avis/doc/avis/Av98a.ps](http://cgm.cs.mcgill.ca/%7Eavis/doc/avis/Av98a.ps)  
   In: Polytopes - Combinatorics and Computation, Ed. G. Kalai and G.
Ziegler, Birkhauser-Verlag (2000) 177-198.  

D. Avis, "Computational Experience with the Reverse Search Vertex
Enumeration Algorithm," Optimization Methods and Software, (1998 (to
appear)).
[http://cgm.cs.mcgill.ca/~avis/doc/avis/Av98b.ps](http://cgm.cs.mcgill.ca/%7Eavis/doc/avis/Av98b.ps)

D. Avis, D. Bremner, and R. Seidel, "How Good are Convex Hull
Algorithms?," Computational Geometry: Theory and Applications, Vol
7,pp.265-301(1997).
[http://cgm.cs.mcgill.ca/~avis/doc/avis/ABS96a.ps](http://cgm.cs.mcgill.ca/%7Eavis/doc/avis/ABS96a.ps)

D. Avis and L. Devroye, "Estimating the Number of Vertices of a
Polyhedron," pp. 179-190 in Snapshots of Computational and Discrete
Geometry, ed. D. Avis and P. Bose, School of Computer Science, McGill
University (1994).
[http://cgm.cs.mcgill.ca/~avis/doc/avis/AD94a.ps](http://cgm.cs.mcgill.ca/%7Eavis/doc/avis/AD94a.ps)  
  In: Information Processing Letters, (2000) V. 73, pp. 137-143.  

D. Avis and K. Fukuda, "A Pivoting Algorithm for Convex Hulls and Vertex
Enumeration of Arrangements and Polyhedra," Discrete and Computational
Geometry, Vol. 8, pp. 295-313 (1992). 
[http://cgm.cs.mcgill.ca/~avis/doc/avis/AF92b.ps](http://cgm.cs.mcgill.ca/%7Eavis/doc/avis/AF92b.ps)

D. Avis, K. Fukuda and S. Picozzi, "On Canonical Representations of
Convex Polyhedra", Mathematical Software,  ICMS 2002, Ed. A. Cohen, X-S
Gao, N. Takayama, World Scientific, pp.350-360 (2002) 
 [http://cgm.cs.mcgill.ca/~avis/doc/avis/AFP02a.ps](http://cgm.cs.mcgill.ca/%7Eavis/doc/avis/AFP02a.ps)  

D. Avis, G. Rosenberg, R. Savani, B. von Stengel, "Enumeration of Nash
Equilibria for Two-Player Games", Economic Theory 42(2009) 9-37 
[pdf](http://cgm.cs.mcgill.ca/%7Eavis/doc/avis/ARSS09a.pdf)

D. Bremner, K. Fukuda and A. Marzetta, Primal-Dual Methods for Vertex
and Facet Enumeration, 13th ACM  Symposium on Computational Geometry SCG
1997, 49-56.   <http://www.cs.unb.ca/profs/bremner/pd/>

  
  
  

  
