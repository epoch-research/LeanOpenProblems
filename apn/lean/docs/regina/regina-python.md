<!-- Vendored from https://regina-normal.github.io/docs/ (Regina handbook, version 7.4; nearest available to installed regina 7.3): pages python, python-access, python-docs, python-snappy, sessions, man-regina-python, plus the Census class page from https://regina-normal.github.io/engine-docs/; converted to markdown -->


## Chapter 9. Python Scripting

**Table of Contents**



























Regina contains inbuilt scripting, which offers you fine control over
Regina's mathematical engine and enables you to automate large amounts
of processing. You can write and run scripts from directly within
Regina, or you can use the separate command-line tool
.

The user interface will stay in sync with any changes that you make
through a script, which means you can happily modify a data file via
scripts while you have it open.

All scripts in Regina use the Python programming language
(). The specific Python
version must be chosen at build time. If you download a ready-made
package then the packager has already chosen the Python version for you;
the ready-made packages on the Regina website will always use the
default version of Python on each system where possible.

### Warning

Regina's Python interface typically assumes you know what you are doing,
and so the onus is on you to follow the rules. All constraints,
preconditions and so on are thoroughly documented in the . Probably the
easiest way to crash Regina is to bring up a Python console and do
something “illegal” (like gluing together two tetrahedra that belong to
different triangulations).

## Starting a Python Session

There are several ways of starting a Python session to work with Regina:

### Graphical Python Consoles

You can open a graphical Python console by selecting Tools→Python
Console from the menu (or by pressing the corresponding toolbar button).

!

A new console window will open as illustrated below, with an input area
down the bottom (see the red arrow) and a full history of the session in
the main part of the window. You can save this history by selecting
Console→Save Session.

!

When you start the Python session, Regina will set some special
variables for you:

`item`  
If you have a packet selected in the tree when you start the Python
session, the variable `item` will refer to this packet (see the figure
above for an example of this).

Note that, if you later change your selection in the packet tree, the
`item` variable will not change as a result.

`root`  
The variable `root` will refer to the hidden root at the top of your
packet tree (this root is not visible in the user interface, but its
top-level children are).

You are welcome to use these variables to change packets in your data
file (or even add, remove or rename packets): the graphical user
interface will always stay in sync with any changes that you make via
Python.

### Command-Line Sessions

You can run the command-line program
 without a
graphical user interface at all. This will use the standard Python
interpreter. Since this is a text-based interface, you can also redirect
input and output in the usual way (using \< and \> in your command
shell).

!

macOS users will find **regina-python** inside Regina's application
bundle. See the 
for details.

Windows users do not have the command-line **regina-python** at all,
though they can still use  and
.

### Script Packets

You can create a new  in your data
file. Script packets allow you to save Python scripts along with your
data, and they give your scripts easy access to the packets inside your
file.

!

When you open a script packet, you will see your Python code in the
lower part of the script editor, and a table of variables up the top.

!

You can add your own variables to this table, and set them to arbitrary
packets within your data file. Regina will always set these variables to
the corresponding packets before running your script.

!

At the top of the script editor you will find buttons to compile and run
your script. Compiling is optional: it merely gives you a chance to spot
syntax errors as you go. When you press Run, Regina will run your script
in a new graphical Python console. The console will be left open in case
you wish to experiment further.

!

Again, you are welcome to change packets in your data file via scripts
(or even add, remove or rename packets): the graphical user interface
will always stay in sync with any changes that your scripts make.

## Accessing Regina from Python

All of Regina's objects, classes and methods belong to the module called
*`regina`*. For instance, the main 3-manifold triangulation class is
`regina.Triangulation3`, the main knot/link class is `regina.Link`, and
the main routine to read a data file is `regina.open`.

### Automatic Imports

Whenever Regina gives you access to Python (either through a , a , or a
), it will
automatically import the *`regina`* module (i.e., “`import regina`”),
and it will import all of Regina's objects, classes and methods into the
current namespace (i.e., “`from regina import *`”). As a single
exception, it will *not* import `regina.open`, so as to not hide
Python's own `open()` function.

This means, for instance, that you can create a new triangulation by
just calling `Triangulation3()`, but to read a data file you should
still call `regina.open(filename)`. For command-line sessions, if you
wish to avoid the heavy-handed “`from regina import *`”, you can pass
the option `--noautoimport` to **regina-python** (in which case you will
need to use fully qualified names such as `regina.Triangulation3()`).

## API Documentation

Regina includes a complete API reference for its calculation engine,
which describes in detail the objects, classes and methods that are
available through Python. To read this documentation, you can:

- read the locally installed documentation by selecting Help→Python API
  Reference;
- read it online through the ;
- read it inline from 
  (see below).

Be aware that this API documentation is primarily written for C++ (the
main language that Regina is written in). This means:

- The documentation uses C++ notation and C++ types, though these are
  all translated in the natural way to Python (e.g., `std::string`
  becomes a Python string, and `std::vector` becomes a Python list).
- Some functions differ in how they are called from C++ versus Python.
  In such cases you will see the C++ description, but there will also be
  a “Python” paragraph explaining how things differ in Python.

There are more issues that Python users should be aware of; please do
read the 
that outlines the main differences.

### Inline Documentation

Since version; 7.2, Regina now provides Python docstrings for all of its
classes and functions. This means that you can get help directly from
the Python prompt, as illustrated below.

Be aware, however, that this documentation is extracted automatically
from the hand-written C++ API documentation discussed above. Although
great attention has been paid to making this extraction as useful and
natural as possible, it is still automated. Therefore you will find:

- The documentation still uses some C++ terminology (e.g.,
  `std::string`, pointers and references, move semantics, etc.).
- Function arguments are often not named in the synopsis at the
  beginning of the docstring (you will see them called `arg0`, `arg1`,
  etc.). However, they *are* named in the detailed descriptions of the
  arguments that follow.
- Some functions differ in how they are called from C++ versus Python
  (e.g., `Tetrahedron3.face()`, or `Link.rewrite()`). In these cases,
  the detailed hand-written argument descriptions will follow the C++
  variant, but the initial synopsis will be written for Python. For
  clarity, here the arguments in the Python synopsis *will* be named.
  Look also for a “Python” paragraph that explains exactly how the C++
  and Python versions differ.
- Some parts of the documentation are not accessible at all through
  Python, since they do not correspond to entities that hold docstrings
  (e.g., class constants such as `Perm4::nPerms`, or standalone pages
  such as the discussion on Seifert fibred space notation).

Ultimately, *it is the C++ documentation that is authoritative*, not the
inline Python documentation. Again, remember that you can always .

An example of docstrings for member functions:

``` programlisting
>>> help(NormalSurface.components)
Help on instancemethod in module regina.engine:

components(...)
    components(self: regina.NormalSurface) -> List[regina.NormalSurface]
    
    Splits this surface into connected components.
    
    A list of connected components will be returned. These components will
    always be encoded using standard (tri-quad or tri-quad-oct)
    coordinates, regardless of the internal vector encoding that is used
    by this surface.
    
    Precondition:
        This normal surface is embedded (not singular or immersed).
    
    Precondition:
        This normal surface is compact (has finitely many discs).
    
    .. warning::
        This routine explicitly builds the normal discs, and so may run
        out of memory if the normal coordinates are extremely large.
    
    Returns:
        the list of connected components.
```

An example of docstrings for classes:

``` programlisting
>>> help(Crossing)
Help on class Crossing in module regina.engine:

class Crossing(pybind11_builtins.pybind11_object)
 |  Represents a single crossing in a link diagram. The two strands of the
 |  link that run over and under the crossing respectively can be accessed
 |  through routines such as over(), under(), upper(), lower(), and
 |  strand().
 |  
 |  Each crossing has a sign, which is either positive (denoted by +1) or
 |  negative (denoted by -1):
 |  
 |  * In a positive crossing, the upper strand passes over the lower
 |    strand from left to right:
 |  
 |  ```
 |    -----\ /----->
 |          \
 |    -----/ \----->
 |  ```
 |  
 |  * In a negative crossing, the upper strand passes over the lower
 |    strand from right to left:
 |  
 |  ```
 |    -----\ /----->
 |          /
 |    -----/ \----->
 |  ```
 |  
 |  If a link has *n* crossings, then these are numbered 0,...,*n*-1. The
 |  number assigned to this crossing can be accessed by calling index().
 |  Note that crossings in a link may be reindexed when other crossings
 |  are added or removed - if you wish to track a particular crossing
 |  through such operations then you should use a pointer to the relevant
 |  Crossing object instead.
 |  
 |  ... (documentation continues) ...
```

## Talking with SnapPy

Since Regina 4.95, a default installation of Regina can talk directly
with a default installation of SnapPy on many platforms. This includes
macOS 10.7 or greater (if you installed the SnapPy app bundle in the
usual `Applications` folder), and GNU/Linux (if your SnapPy uses the
default system Python installation).

Simply type **`import snappy`** from within any of Regina's Python
environments. To send information back and forth between Regina and
SnapPy:

- Regina's triangulation classes `Triangulation3` and
  `SnapPeaTriangulation` both have a `snapPea()` function, which gives a
  string that you can pass to SnapPy's `Manifold` constructor.

- SnapPy's `Manifold` class has a `_to_string()` function, which gives a
  string that you can pass to Regina's `Triangulation3` or
  `SnapPeaTriangulation` constructor.

Regarding fillings and peripheral curves: Regina does not store fillings
or peripheral curves for its own native ,
as represented by the `Triangulation3` class. However, it does store
fillings and peripheral curves for its hybrid , as
represented by the `SnapPeaTriangulation` class. The trade-off is that
the native `Triangulation3` class offers Regina's full fine-grained
control over the triangulation, whereas the hybrid
`SnapPeaTriangulation` class has a more limited (largely read-only)
interface.

- When sending data from Regina to SnapPy, if your triangulation is of
  the class `Triangulation3`, then `Triangulation3.snapPea()` will
  create a SnapPy manifold in which all fillings and peripheral curves
  are marked as unknown. If your triangulation is of the class
  `SnapPeaTriangulation`, and if you already have fillings and
  peripheral curves stored on each cusp, then
  `SnapPeaTriangulation.snapPea()` will create a SnapPy manifold that
  preserves these.

- Conversely, when sending data from SnapPy to Regina, you can choose to
  instantiate a triangulation using either the `Triangulation3` class or
  the `SnapPeaTriangulation` class. If you use the `Triangulation3`
  class then all fillings and peripheral curves will be lost. If you use
  the `SnapPeaTriangulation` class then fillings and peripheral curves
  will be preserved (but your interface will be more restricted).

If you wish to send the complement of a native Regina `Link` to SnapPy,
you can pass your link directly to the `SnapPeaTriangulation`
constructor, which will preserve the peripheral curves from the link
diagram; then you can pass this to SnapPy via
`SnapPeaTriangulation.snapPea()` as above.

Regarding the interface: the `SnapPeaTriangulation` class inherits from
`Triangulation3`, and so you can use it anywhere that a read-only
triangulation is expected (in particular, you can use it for enumerating
vertex normal surfaces or angle structures). However, because
`SnapPeaTriangulation` must maintain two synchronised copies of the
triangulation (Regina's and SnapPea's), it is essentially read-only: any
attempt to modify the triangulation using Regina's native routines
(e.g., `pachner()` or `barycentricSubdivision()`) will cause the SnapPea
triangulation to delete itself and become a “null triangulation”
instead.

### Warning

At present, SnapPy (version 2.0.3) is not compatible with multiple
Python interpreters. If you import SnapPy into more than one Python
console in the graphical user interface, SnapPy may stop working. See

for details.

The following Python session illustrates several of the concepts
discussed above.

``` programlisting
bab@ember:~$ regina-python 
Regina 7.2
Software for low-dimensional topology
Copyright (c) 1999-2022, The Regina development team
>>> import snappy
>>> m = snappy.Manifold('m001')
>>> t = SnapPeaTriangulation(m._to_string())
>>> print t.detail()
Size of the skeleton:
  Tetrahedra: 2
  Triangles: 4
  Edges: 2
  Vertices: 1

Tetrahedron gluing:
  Tet  |  glued to:      (012)      (013)      (023)      (123)
  -----+-------------------------------------------------------
    0  |               1 (103)    1 (320)    1 (210)    1 (132)
    1  |               0 (320)    0 (102)    0 (310)    0 (132)

Vertices:
  Tet  |  vertex:    0   1   2   3
  -----+--------------------------
    0  |             0   0   0   0
    1  |             0   0   0   0

Edges:
  Tet  |  edge:   01  02  03  12  13  23
  -----+--------------------------------
    0  |           0   1   1   1   1   0
    1  |           0   1   1   1   1   0

Triangles:
  Tet  |  face:  012 013 023 123
  -----+------------------------
    0  |           0   1   2   3
    1  |           2   0   1   3

Tetrahedron shapes:
  0: ( -1.60812e-16, 1 )
  1: ( -1.60812e-16, 1 )

Cusps:
  0: Vertex 0, complete

>>> print t.hasStrictAngleStructure()
True
>>> print AngleStructures(t).detail()
4 vertex angle structures (no restrictions):
0 1 0 ; 1 0 0
0 0 1 ; 1 0 0
1 0 0 ; 0 1 0
1 0 0 ; 0 0 1

>>> t2 = Example3.figureEight()
>>> m2 = snappy.Manifold(t2.snapPea())
>>> print m2.volume()
2.02988321282
>>>
  
```

## Sample Python Sessions

Several sample Python sessions are reproduced below. Each session was
started by running **`regina-python`** from the command line.

### Working with a triangulation

``` programlisting
example$ regina-python
Regina 7.0
Software for low-dimensional topology
Copyright (c) 1999-2021, The Regina development team
>>> ################################
>>> #
>>> #  Sample Python Script
>>> #
>>> #  Illustrates different queries and actions on a 3-manifold triangulation
>>> #  and its normal surfaces.
>>> #
>>> #  See the file "triangulation.session" for the results of running this
>>> #  script.
>>> #
>>> ################################
>>>
>>> # Create a new (3,4,7) layered solid torus.  This is a 3-tetrahedron
>>> # triangulation of a solid torus.
>>> t = Example3.lst(3, 4)
>>> print(t)
Bounded orientable 3-D triangulation, f = ( 1 5 7 3 )
>>>
>>> # Print the full skeleton of the triangulation.
>>> print(t.detail())
Size of the skeleton:
  Tetrahedra: 3
  Triangles: 7
  Edges: 5
  Vertices: 1

Tetrahedron gluing:
  Tet  |  glued to:      (012)      (013)      (023)      (123)
  -----+-------------------------------------------------------
    0  |              boundary   boundary    1 (012)    1 (130)
    1  |               0 (023)    0 (312)    2 (013)    2 (120)
    2  |               1 (312)    1 (023)    2 (312)    2 (230)

Vertices:
  Tet  |  vertex:    0   1   2   3
  -----+--------------------------
    0  |             0   0   0   0
    1  |             0   0   0   0
    2  |             0   0   0   0

Edges:
  Tet  |  edge:   01  02  03  12  13  23
  -----+--------------------------------
    0  |           0   1   2   2   1   3
    1  |           1   2   3   3   2   4
    2  |           2   4   3   3   4   3

Triangles:
  Tet  |  face:  012 013 023 123
  -----+------------------------
    0  |           0   1   2   3
    1  |           2   3   4   5
    2  |           5   4   6   6

>>>
>>> # Calculate some algebraic properties of the triangulation.
>>> print(t.homology())
Z
>>> print(t.homologyBdry())
2 Z
>>>
>>> # Test for 0-efficiency, which asks Regina to search for certain types
>>> # of normal surfaces.
>>> print(t.isZeroEfficient())
False
>>>
>>> # Make our own list of vertex normal surfaces in standard coordinates.
>>> surfaces = NormalSurfaces(t, NormalCoords.Standard)
>>>
>>> # Print the full list of vertex normal surfaces.
>>> print(surfaces.detail())
Embedded, vertex surfaces
Coordinates: Standard normal (tri-quad)
Number of surfaces is 9
1 1 1 1 ; 0 0 0 || 1 1 0 0 ; 1 0 0 || 0 0 0 0 ; 0 2 0
0 0 1 1 ; 1 0 0 || 1 1 1 1 ; 0 0 0 || 1 1 1 1 ; 0 0 0
0 0 0 0 ; 0 2 0 || 0 0 1 1 ; 1 0 0 || 1 1 1 1 ; 0 0 0
0 0 0 0 ; 0 0 2 || 0 0 0 0 ; 0 2 0 || 0 0 1 1 ; 1 0 0
1 1 0 0 ; 0 0 1 || 1 1 0 0 ; 0 0 0 || 0 0 0 0 ; 0 1 0
3 3 0 0 ; 0 0 1 || 1 1 0 0 ; 0 0 2 || 1 1 0 0 ; 0 0 1
0 0 1 1 ; 1 0 0 || 1 1 0 0 ; 1 0 0 || 0 0 0 0 ; 0 2 0
0 0 0 0 ; 0 1 0 || 0 0 0 0 ; 1 0 0 || 0 0 0 0 ; 0 1 0
1 1 1 1 ; 0 0 0 || 1 1 1 1 ; 0 0 0 || 1 1 1 1 ; 0 0 0

>>>
>>> # Print the Euler characteristic and orientability of each surface.
>>> for s in surfaces:
...     print("Chi =", s.eulerChar(), "; Or =", s.isOrientable())
...
Chi = -1 ; Or = True
Chi = 0 ; Or = True
Chi = 0 ; Or = True
Chi = 0 ; Or = True
Chi = 0 ; Or = False
Chi = 1 ; Or = True
Chi = -2 ; Or = True
Chi = -1 ; Or = False
Chi = 1 ; Or = True
>>>
>>> # List all surfaces with more than one quad in the first tetrahedron.
>>> for s in surfaces:
...     if s.quads(0,0) + s.quads(0,1) + s.quads(0,2) > 1:
...         print(s)
...
0 0 0 0 ; 0 2 0 || 0 0 1 1 ; 1 0 0 || 1 1 1 1 ; 0 0 0
0 0 0 0 ; 0 0 2 || 0 0 0 0 ; 0 2 0 || 0 0 1 1 ; 1 0 0
>>>
```

### Working with a packet tree

``` programlisting
example$ regina-python
Regina 7.0
Software for low-dimensional topology
Copyright (c) 1999-2021, The Regina development team
>>> ################################
>>> #
>>> #  Sample Python Script
>>> #
>>> #  Illustrates the traversal and manipulation of an entire packet tree.
>>> #
>>> #  See the file "tree.session" for the results of running this script.
>>> #
>>> ################################
>>>
>>> # Recreate the original SnapPea census of cusped hyperbolic manifolds
>>> # triangulated by at most 5 tetrahedra.
>>> #
>>> # Since we are building a packet tree, we need to use PacketOfTriangulation3,
>>> # not the plain type Triangulation3 (which is not a packet type).
>>> census = Container()
>>> for i in range(415):
...     mfd = SnapPeaCensusManifold(SnapPeaCensusManifold.SEC_5, i)
...     census.append(make_packet(mfd.construct(), mfd.name()))
...
>>> # The triangulations are now all children of the "census" container.
>>> # Remove all triangulations with more than two tetrahedra.
>>> #
>>> # Since we are deleting children, we step through the children manually
>>> # instead of just iterating over children().
>>> tri = census.firstChild()
>>> while tri != None:
...     next = tri.nextSibling()
...     if tri.size() > 2:
...         tri.makeOrphan()
...     tri = next
...
>>> # Print the homology of each remaining triangulation.
>>> # This time we are not adding or removing children, so we can just iterate.
>>> for tri in census.children():
...     print(tri.label() + ":", tri.homology())
...
Gieseking manifold: Z
SnapPea m001: Z + Z_2
SnapPea m002: Z + Z_2
SnapPea m003: Z + Z_5
Figure eight knot complement: Z
>>>
```

### Reporting progress of long operations

``` programlisting
example$ regina-python
Regina 7.0
Software for low-dimensional topology
Copyright (c) 1999-2021, The Regina development team
>>> ################################
>>> #
>>> #  Sample Python Script
>>> #
>>> #  Illustrates progress reporting during long operations.
>>> #
>>> #  See the file "progress.session" for the results of running this script.
>>> #
>>> ################################
>>>
>>> import threading
>>> import time
>>>
>>> # Create an 18-tetrahedron triangulation of a knot complement with real
>>> # boundary faces (not an ideal vertex).  The knot is L106003 from the
>>> # knot/link census.  We used Regina to truncate the ideal vertex, and
>>> # then copied the isomorphism signature so that we can reconstruct the
>>> # triangulation here.
>>> sig = 'sfLfvQvwwMQQQccjghjkmqlonrnrqpqrnsnksaisnrobocksks'
>>> tri = Triangulation3(sig)
>>> print(tri)
Bounded orientable 3-D triangulation, f = ( 1 20 37 18 )
>>>
>>> # Create a progress tracker to use during the normal surface enumeration.
>>> # This will report the state of progress while the enumeration runs in
>>> # the background.
>>> tracker = ProgressTracker()
>>>
>>> # Start the normal surface enumeration in a new thread.
>>> surfaces = None
>>> def run():
...     global surfaces, tracker
...     surfaces = NormalSurfaces(tri, NormalCoords.Standard, NormalList.Vertex,
...         NormalAlg.Default, tracker)
...
>>> thread = threading.Thread(target = run)
>>> thread.start()
>>>
>>> # At this point the enumeration is up and running.
>>> # Output a progress report every quarter-second until it finishes.
>>> while not tracker.isFinished():
...     print('Progress:', tracker.percent(), '%')
...     time.sleep(0.25)
...
Progress: 0.17578125 %
Progress: 54.20654296875 %
Progress: 91.80555555555556 %
>>>
>>> # The surface enumeration is now complete.
>>> thread.join()
>>> print(surfaces)
2319 embedded, vertex surfaces (Standard normal (tri-quad))
>>>
```

## Name

regina-python — Regina's command-line Python interface

## Synopsis

**regina-python** \[\[`-q, --quiet`\] \| \[`-v, --verbose`\]\]
\[`-n, --nolibs`\] \[`-a, --noautoimport`\]

**regina-python** \[\[`-q, --quiet`\] \| \[`-v, --verbose`\]\]
\[`-n, --nolibs`\] \[`-a, --noautoimport`\] \[`-i, --interactive`\]
{*`script`*} \[*`script-args`*\]

## Description

Regina is a software package for 3-manifold and 4-manifold topologists,
with a focus on triangulations, knots and links, normal surfaces, and
angle structures. For 3-manifolds, it includes high-level tasks such as
3-sphere and unknot recognition, connected sum decomposition and
Hakenness testing, comes with a rich database of census manifolds, and
incorporates the SnapPea kernel for working with hyperbolic manifolds.
For 4-manifolds, it offers a range of combinatorial and algebraic tools,
plus support for normal hypersurfaces. For knots and links, Regina can
perform combinatorial manipulation, compute knot polynomials, and work
with several import/export formats. Regina comes with a full graphical
user interface, as well as Python bindings and a low-level C++
programming interface.

This command starts an interactive Python session for Regina. This will
be a command-line Python session, with direct text input/output and no
graphical user interface. All of the objects, clases and methods from
Regina's mathematical engine will be made available through the module
*`regina`*, which will be imported on startup (effectively running
`import regina`). Moreover, unless the option `--noautoimport` is
passed, all of Regina's objects, classes and methods will be imported
directly into the current namespace (effectively running
`from regina import *`).

Instead of starting an interactive Python session, you can pass a Python
script (with arguments if desired). In this case Regina will run the
script (after first importing the *`regina`* module). If you pass
`--interactive`, Regina will leave you at a Python prompt once the
script finishes; otherwise it will exit Python and return you to the
command line.

## Options

`-q`, `--quiet`  
Start in quiet mode. No output will be produced except for serious
errors. In particular, warnings will be suppressed.

This is equivalent to setting the environment variable
*`REGINA_VERBOSITY`*=`0`.

`-v`, `--verbose`  
Start in verbose mode. Additional diagnostic information will be output.

This is equivalent to setting the environment variable
*`REGINA_VERBOSITY`*=`2`.

`-a`, `--noautoimport`  
Still import the *`regina`* module, but do not automatically import all
of Regina's objects, classes and methods into the current namespace
(that is, do not run `from regina import *`). This means that (for
example) the main 3-manifold triangulation class must be accessed as
`regina.Triangulation3`, not just `Triangulation3`.

`-i`, `--interactive`  
Run the script in interactive mode. After executing the given script,
Regina will leave you in the Python interpreter to run your own
additional commands.

This option is only available when a script is passed. If no script is
passed, **regina-python** will always start in interactive mode.

## Environment Variables

The following environment variables influence the behaviour of this
program. Most variables can also be set in the local configuration file
`~/.regina-python` using a line of the form *`option`*=*`value`*;
exceptions are noted below. Environment variables take precedence over
values in the configuration file.

*`REGINA_VERBOSITY`*  
Specifies how much output should be generated. Recognised values are:

`0`  
Display errors only; this is equivalent to passing the option `--quiet`.

`1`  
Display errors and warnings; this is the default.

`2`  
Display errors, warnings and diagnostic output; this is equivalent to
passing the option `--verbose`.

*`REGINA_PYTHON`*  
The command used to start the Python interpreter.

In general you should use the same version of Python that Regina was
built against; otherwise Python might not be able to load the *`regina`*
module.

Normally you should not need to set this option yourself. By default,
Regina will use the same Python installation that it was built against.

*`REGINA_PYLIBDIR`*  
The directory containing the Python module *`regina`*.

If you have installed Regina's Python module in a standard Python
location (i.e., Python can import it directly without extending
`sys.path`), then *`REGINA_PYLIBDIR`* should be left empty or undefined.

Normally you should not need to set this option yourself. This program
should know how to find Regina's Python module in standard situations,
which include fixed filesystem installations (e.g., GNU/Linux and
Windows), relocatable app bundles (e.g., macOS), and running directly
from the source tree.

*`REGINA_HOME`*  
The directory beneath which Regina's data files are installed. In
particular, Regina's census lookup routines will look for the census
databases in the subdirectory *`$REGINA_HOME`*`/data/census/`.

This option can only be set from the environment: it cannot be set in
the configuration file `~/.regina-python`.

Normally you should not need to set this option yourself. This program
should know how to find its data files in standard situations, which
include fixed filesystem installations (e.g., GNU/Linux and Windows),
relocatable app bundles (e.g., macOS), and running directly from the
source tree.

## macOS Users

If you downloaded a drag-and-drop app bundle, this utility is shipped
inside it. If you dragged Regina to the main Applications folder, you
can run it as `/Applications/Regina.app/Contents/MacOS/regina-python`.

## Windows Users

The command **regina-python** is not available under Windows. However,
you can still use Python scripting in Regina's graphical user interface,
by opening a graphical Python console or using script packets.

## See Also

.

Regina comes with thorough API documentation, which describes in detail
all of the objects, classes and methods that Regina makes available to
Python. You can access this documentation via Help→Python API Reference
in the graphical user interface, or read it online at
.

## Author

Many people have been involved in the development of Regina; see the
 for a full list
of credits.

- 
- 

 \| 

regina::Census Class Reference



A utility class used to search for triangulations across one or more
3-manifold census databases. 

`#include <census/census.h>`

## Detailed Description

A utility class used to search for triangulations across one or more
3-manifold census databases.

This class consists of static routines only. The main entry point (and
typically the only way that you would use this class) is via the various
static

routines.

Warning  
This class is not thread-safe, in that it performs some global
initialisation the first time one of the

functions is called. If you need thread-safety, you can always call

with an empty string when initialising your program, and ensure this has
finished before you allow any subsequent "normal" calls to

from other threads.

## Member Function Documentation

## lookup() \[1/2\]

Searches for the given triangulation through all of Regina's in-built
census databases.

For this routine you specify the triangulation by giving its isomorphism
signature, as returned by
.
This is faster than the variant ,
since Regina's census databases store isomorphism signatures internally.
If you do not already know the isomorphism signature, it is fine to just
call 
instead.

Note that there may be many hits (possibly from multiple databases, and
in some cases possibly even within the same database). Therefore a
*list* of hits will be returned, which you can iterate through the
individual matches. Even if there are no matches at all, a list will
still be returned; you can call empty() on this list to test whether any
matches were found.

This routine is fast: it first computes the isomorphism signature of the
triangulation, and then performs a logarithmic-time lookup in each
database (here "logarithmic" means logarithmic in the size of the
database).

Parameters  

&nbsp;

Returns  
a list of all database matches.

## lookup() \[2/2\]

Searches for the given triangulation through all of Regina's in-built
census databases.

Internally, the census databases store isomorphism signatures as opposed
to fully fleshed-out triangulations. If you already have the isomorphism
signature of the triangulation, then you can call the variant

instead, which will be faster since it avoids some extra overhead.

Note that there may be many hits (possibly from multiple databases, and
in some cases possibly even within the same database). Therefore a
*list* of hits will be returned, which you can iterate through the
individual matches. Even if there are no matches at all, a list will
still be returned; you can call empty() on this list to test whether any
matches were found.

This routine is fast: it first computes the isomorphism signature of the
triangulation, and then performs a logarithmic-time lookup in each
database (here "logarithmic" means logarithmic in the size of the
database).

Parameters  

&nbsp;

Returns  
a list of all database matches.

------------------------------------------------------------------------

The documentation for this class was generated from the following file:

- census/

------------------------------------------------------------------------

Copyright © 1999–2025, The Regina development team

