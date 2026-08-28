<!-- Vendored from https://github.com/polymake/polymake (tag V4.6) demo notebooks perl_intro, apps_polytope, properties, lattice_polytopes_tutorial (converted from ipynb) and https://polymake.org/doku.php/user_guide/howto/scripting (Calling/Structure/Location sections), polymake 4.6 -->

# polymake 4.6 usage

Start the interactive shell with `polymake`. Run a script non-interactively with `polymake --script <file>` (see the Scripting section at the end). The shell language is polymake/Perl.

# Using Perl within polymake

The language that the interactive version of `polymake` speaks is a dialect of Perl that we refer to as `polymake`/Perl. See [www.perl.org](http://www.perl.org) for comprehensive Perl information.  Note also that the ordinary Perl manual pages are particularly useful, especially the perlintro man page which is also available on [perldoc](http://perldoc.perl.org/perlintro.html).  This short section here cannot be a replacement for a thorough introduction to this language, but we want to focus on a few key points that are relevant to `polymake`.

### Standard data structures

The Perl programming language originally provides three different data structures, scalars(`$`), arrays(`@`), and hashes(`%`). The user always has to specify the type of a variable using the appropriate symbol `$`, `@`, or `%`. If you forget to do so, you will receive the following error message:

    > i=5;
    polymake:  ERROR: Unquoted string "i" may clash with future reserved word.

    



Here are some simple commands illustrating how to use the different data structures:
##### Scalars


```perl
$i=5;
$j=6;
$sum=$i+$j; print $sum;
```
Output:
```
11
```


##### Arrays

    


```perl
@array=("a","b","c"); print scalar(@array);
push(@array,"d"); print "@array"; 
$first_entry=$array[0]; print $first_entry;
print join("\n",@array);
@array2=(3,1,4,2);
print sort(@array2);
```
Output:
```
3a b c daa
b
c
d1234
```


##### Hashes

    


```perl
%hash=();
$hash{"zero"}=0;
$hash{"four"}=4;
print keys %hash;
print join(", ",keys %hash);
print join(", ",values %hash);
%hash=("one",1,"two",2);
%hash=("one"=>1,"two"=>2);
```
Output:
```
fourzerofour, zero4, 0
```


### `polymake`-Perl

In addition to the three standard data structures, the enriched version of `Perl` used in `polymake` also provides special data structures for dealing with more complicated concepts. For an introduction to the polymake object model see [here](properties.ipynb#Objects).

`polymake`'s object hierarchy is completely reflected on the Perl side. Let us create a small polytope as an example object.

    


```perl
$p = new Polytope(POINTS=>[[1,0,1],[1,0,-1],[1,1,0],[1,-1,0]]);
```


Note that the `Perl`-type of the variable `$p` is `Scalar`, as the variable is internally treated as a reference to a `C++`-object. The true nature of the object becomes visible if it is printed:

    


```perl
print $p;
```
Output:
```
Polymake::polytope::Polytope__Rational=ARRAY(0x55c8aa54c778)
```

In this case it is a `polymake` object from the application `polytope`, and it happens to be of type `Polytope<Rational>`. Technically, `$p` is a reference to an array (but it should be never treated as an array unless you are deliberately trying to crash `polymake`). If you want less technical information on the type of your object, use this:

```perl
print $p->type->full_name;
```
Output:
```
Polytope<Rational>
```


#### "Small objects": Data structures inherited from C++

You can use objects that are inherited from the `C++`-side of `polymake` in the interactive shell. A complete list of so-called "small objects" can be found in the [online documentation](https://polymake.org/doku.php/documentation/latest/common#property_types).
Here is a selection of three different structures that facilitate everyday work with `polymake`:
##### Arrays

The small object `Array` can be initialized in different ways and with different template parameters:

    


```perl
@array=("a","b","c");
$arr1=new Array<String>(\@array); print $arr1;
$arr2=new Array<Int>([3,2,5]); print $arr2;
$arr3=new Array<Int>(0,1,2,3); print $arr3;
$arr4=new Array<Int>(0..4); print $arr4;
$arr5=new Array<Int>($arr4); print $arr5;
```
Output:
```
a b c3 2 50 1 2 30 1 2 3 40 1 2 3 4
```


You have random access:

    


```perl
$arr5->[0] = 100;
print $arr5;
```
Output:
```
100 1 2 3 4
```

 It is also possible to convert the `C++`-object `Array` into a `Perl`-array by writing 

    


```perl
@arr4=@{$arr4}; print $arr2;
```
Output:
```
3 2 5
```


 or simply

    


```perl
@arr4=@$arr4;
```


##### Sets

On `C++`-side sets are stored in a balanced binary search (AVL) tree. For more information see the [PTL-documentation](https://polymake.org/release_docs/master/PTL/classpm_1_1Set.html). In many cases, the small objects can be converted into `Perl`-types in the expected way: 

    


```perl
$set=new Set<Int>(3,2,5); print $set;
print $set->size;
@array_from_set=@$set;
```
Output:
```
{2 3 5}3
```


##### Matrices

Here is a simple way to initialize a matrix:

    


```perl
$mat=new Matrix<Rational>([[2,1,4,0,0],[3,1,5,2,1],[1,0,4,0,6]]);
print $mat;
```
Output:
```
2 1 4 0 0
3 1 5 2 1
1 0 4 0 6
```


 You could also define it by passing a reference to an (`Perl`-)array of `Vectors`. The single entries are interpreted as different rows: 

    


```perl
$row1=new Vector<Rational>([2,1,4,0,0]);
$row2=new Vector<Rational>([3,1,5,2,1]);
$row3=new Vector<Rational>([1,0,4,0,6]);
@matrix_rows=($row1,$row2,$row3);
$matrix_from_array=new Matrix<Rational>(\@matrix_rows);
```


 You can change a single entry of a matrix in the following way (if it is not already assigned to an immutable property like `VERTICES`!):

    


```perl
$mat->row(1)->[1]=7;
print $mat->row(1)->[1], "\n";
print $mat, "\n";
$mat->elem(1,2)=8;
print $mat;
```
Output:
```
7
2 1 4 0 0
3 7 5 2 1
1 0 4 0 6

2 1 4 0 0
3 7 8 2 1
1 0 4 0 6
```


 A unit matrix of a certain dimension can be defined via the user-function `unit_matrix<COORDINATE_TYPE>(.)`: 

    


```perl
$unit_mat=4*unit_matrix<Rational>(3);
print $unit_mat;
```
Output:
```
(3) (0 4)
(3) (1 4)
(3) (2 4)
```


 The reason for the "strange output" is the implementation as *sparse matrix*: 

    


```perl
print ref($unit_mat);
```
Output:
```
Polymake::common::SparseMatrix_A_Rational_I_NonSymmetric_Z
```


However, some functions cannot deal with this special type of matrix. In this case it is necessary to transform the sparse matrix into a dense matrix first via:

    


```perl
$dense=new Matrix<Rational>($unit_mat);print $dense;
```
Output:
```
4 0 0
0 4 0
0 0 4
```


 or just

    


```perl
$dense2=dense($unit_mat);print $dense2;
```
Output:
```
4 0 0
0 4 0
0 0 4
```


 You can also work with matrices that have different types of coordinates like `Rational`, `Float`, or `Int`: 

    


```perl
$m_rat=new Matrix<Rational>(3/5*unit_matrix<Rational>(5)); print $m_rat, "\n"; 
$m2=$mat/$m_rat; print $m2, "\n";
$m_int=new Matrix<Int>(unit_matrix<Rational>(5)); print $m_int, "\n";
```
Output:
```
3/5 0 0 0 0
0 3/5 0 0 0
0 0 3/5 0 0
0 0 0 3/5 0
0 0 0 0 3/5

2 1 4 0 0
3 7 8 2 1
1 0 4 0 6
3/5 0 0 0 0
0 3/5 0 0 0
0 0 3/5 0 0
0 0 0 3/5 0
0 0 0 0 3/5

1 0 0 0 0
0 1 0 0 0
0 0 1 0 0
0 0 0 1 0
0 0 0 0 1
```

Sometimes there is incompatible types:
```perl
> $m3=$m_rat/$m_int;
```
```
C++/perl Interface module compilation failed; most likely due to a type mismatch.
Set the variable $Polymake::User::Verbose::cpp to a positive value and repeat for more details.
```

The error message indicates that you need to convert the integer matrix to a rational matrix first:

```perl
$m3=$m_rat/(convert_to<Rational>($m_int)); print $m3;
```
Output:
```
3/5 0 0 0 0
0 3/5 0 0 0
0 0 3/5 0 0
0 0 0 3/5 0
0 0 0 0 3/5
1 0 0 0 0
0 1 0 0 0
0 0 1 0 0
0 0 0 1 0
0 0 0 0 1
```


 By "/" you can add rows to a matrix, whereas "|" adds columns. By the way, this also works for `Vector`.

    


```perl
$z_vec=zero_vector<Int>($m_int->rows);
$extended_matrix=($z_vec|$m_int); print $extended_matrix;
```
Output:
```
0 1 0 0 0 0
0 0 1 0 0 0
0 0 0 1 0 0
0 0 0 0 1 0
0 0 0 0 0 1
```


It is also possible to nest template parameters in any way you like, e.g.

    


```perl
$set=new Set<Int>(3,2,5);
$template_Ex=new Array<Set<Int>>((new Set<Int>(5,2,6)),$set); print $template_Ex; print ref($template_Ex);
```
Output:
```
{2 5 6}
{2 3 5}
Polymake::common::Array__Set__Int
```


However, if you use a template combination, you have never used before, it may take some time until you see the result. This is due to the fact that `polymake` compiles your new combination *on the fly*. But this is only a one-time effect, and next time you use this combination it will work without delay.

#### "Big Objects": Objects with properties

A big object is an instance of a data type which represents a mathematical concept with clear semantics. They may have template parameters.

    


```perl
$p=new Polytope<Rational>(POINTS=>cube(4)->VERTICES);
$lp=new LinearProgram<Rational>(LINEAR_OBJECTIVE=>[0,1,1,1,1]);
```


Big objects have properties which come with a type, which is either built-in or a small object type or a big object type, and which can be accessed using the `-``>` operator.

    


```perl
# access the property named `LP`:
$p->LP=$lp;
# properties can have properties themselves.
print $p->LP->MAXIMAL_VALUE;
```
Output:
```
4
```



Scalar properties can be used in arithmetic expressions right away.

    


```perl
$i = ($p->N_FACETS * $p->N_FACETS) * 15;
```

    


```perl
print $i;
```
Output:
```
960
```

Check out the tutorial on [properties](properties.ipynb) to learn more about the way properties are used and computed.

### A small example script...

...to demonstrate the usage of `polymake`/Perl. You can download the matrix file [here](https://polymake.org/lib/exe/fetch.php/points.demo).



```perl
### load matrix from file
open(INPUT, "< demo/Workshop2011/points.demo");
$matrix=new Matrix<Rational>(<INPUT>);
close(INPUT);
print $matrix;


### create a polytope from the matrix
$p=new Polytope<Rational>(POINTS=>$matrix);
print $p->FACETS;
print $p->DIM;
print $p->VERTEX_SIZES;


### print "simple" vertices
for(my $i=0;$i<scalar(@{$p->VERTEX_SIZES});$i++){
    if($p->VERTEX_SIZES->[$i]==$p->DIM){
    print $i.": ".$p->VERTICES->row($i)."\n";
    }
}


### put their indices in a set
$s=new Set<Int>();
for(my $i=0;$i<scalar(@{$p->VERTEX_SIZES});$i++){
    if($p->VERTEX_SIZES->[$i]==$p->DIM){
    $s+=$i;
    }
}


### iterate the set in two different ways
foreach(@{$s}){
    print $p->VERTICES->row($_)."\n";
}
foreach my $index(@{$s}){
    print $p->VERTICES->row($index)."\n";
}


### create a minor of the vertices matrix that only contains the simple ones
$special_points=$p->VERTICES->minor($s,All); print $special_points;
```
Output:
```
-1
```

### Writing scripts

Comprehensive information on how to use scripts within `polymake` can be found [here](https://polymake.org/doku.php/user_guide/howto/scripting).

# Tutorial on Polytopes

A *polytope* is the convex hull of finitely many points in some Euclidean space. Equivalently, a polytope is the bounded intersection of finitely many affine halfspaces. `polymake` can deal with polytopes in both representations and provides numerous tools for analysis.


This tutorial first shows basic ways of defining a polytope from scratch. For larger input (e.g. from a file generated by some other program) have a look at our HowTo on [loading data](data.ipynb) in `polymake`.


The second part demonstrates some of the tool `polymake` provides for handling polytopes by examining a small example. For a complete list of properties of polytopes and functions that `polymake` provides, see the [polytope documentation](https://polymake.org/doku.php/documentation/latest/polytope).

## Constructing a polytope from scratch

<a name="dokuwiki_friendly_id_of_v_description"></a>
### V-Description

To define a polytope as the convex hull of finitely many points, you can pass a matrix of coordinates to the constructor. Since `polymake` uses [homogeneous coordinates](coordinates.ipynb), you need to set the additional coordinate x<sub>0</sub> to 1.


```perl
$p = new Polytope(POINTS=>[[1,-1,-1],[1,1,-1],[1,-1,1],[1,1,1],[1,0,0]]);
```


The `POINTS` can be any set of coordinates, they are not required to be irredundant nor vertices of their convex hull. To compute the actual vertices of our polytope, we do this:

    


```perl
print $p->VERTICES;
```
Output:
```
1 -1 -1
1 1 -1
1 -1 1
1 1 1
```

You can also add a lineality space via the input property `INPUT_LINEALITY`.

    


```perl
$p2 = new Polytope(POINTS=>[[1,-1,-1],[1,1,-1],[1,-1,1],[1,1,1],[1,0,0]],INPUT_LINEALITY=>[[0,1,0]]);
```


To take a look at what that thing looks like, you can use the `VISUAL` method:

    


```perl
$p2->VISUAL;
```


See [here](visual_tutorial.ipynb#application-polytope) for details on visualizing polytopes.

 If you are sure that all the points really are *extreme points* (vertices) and your description of the lineality space is complete, you can define the polytope via the properties `VERTICES` and `LINEALITY_SPACE` instead of `POINTS` and `INPUT_LINEALITY`. This way, you can avoid unnecessary redundancy checks.



 The input properties `POINTS` / `INPUT_LINEALITY` may not be mixed with the properties `VERTICES` / `LINEALITY_SPACE`. Furthermore, the `LINEALITY_SPACE` **must be specified** as soon as the property `VERTICES` is used:

    


```perl
$p3 = new Polytope<Rational>(VERTICES=>[[1,-1,-1],[1,1,-1],[1,-1,1],[1,1,1]], LINEALITY_SPACE=>[]);
```


### H-Description

It is also possible to define a polytope as an intersection of finitely many halfspaces, i.e., a matrix of inequalities.



An inequality a<sub>0</sub> + a<sub>1</sub> x<sub>1</sub> + ... + a<sub>d</sub> x<sub>d</sub> >= 0 is encoded as a row vector (a<sub>0</sub>,a<sub>1</sub>,...,a<sub>d</sub>), see also [Coordinates for Polyhedra](coordinates.ipynb). Here is an example:

    


```perl
$p4 = new Polytope(INEQUALITIES=>[[1,1,0],[1,0,1],[1,-1,0],[1,0,-1],[17,1,1]]);
```


To display the inequalities in a nice way, use the `print_constraints` method.

    


```perl
print_constraints($p4->INEQUALITIES);
```
Output:
```
0: x1 >= -1
1: x2 >= -1
2: -x1 >= -1
3: -x2 >= -1
4: x1 + x2 >= -17
5: 0 >= -1
```

The last inequality means 17+x<sub>1</sub>+x<sub>2</sub> >= 0, hence it does not represent a facet of the polytope. If you want to take a look at the acutal facets, do this:

    


```perl
print $p4->FACETS;
```
Output:
```
1 1 0
1 0 1
1 -1 0
1 0 -1
```


If your polytope lies in an affine subspace then you can specify its equations via the input property `EQUATIONS`.



    


```perl
$p5 = new Polytope(INEQUALITIES=>[[1,1,0,0],[1,0,1,0],[1,-1,0,0],[1,0,-1,0]],EQUATIONS=>[[0,0,0,1],[0,0,0,2]]);
```


Again, if you are sure that all your inequalities are facets, you can use the properties `FACETS` and `AFFINE_HULL` instead. Note that this pair of properties is dual to the pair `VERTICES` / `LINEALITY_SPACE` described above.


## Convex Hull Computations

Of course, `polymake` can convert the V-description of a polytope to its H-description and vice versa. In fact, this is done automatically whenever you ask for a suitable property.

For instance, continuing with the example above, the following triggers a dual convex hull computation.  Note that this particular command does not compute any output.

```perl
$p5->VERTICES;
```

Printing the vertices later does *not* result in a recomputation.  Known properties are stored. 

```perl
print $p5->VERTICES;
```
Output:
```
1 1 -1 0
1 1 1 0
1 -1 1 0
1 -1 -1 0
```

Depending on the individual configuration polymake chooses one of the several convex hull computing algorithms that have a `polymake` interface. Available algorithms are double description ([cdd](http://www.ifor.math.ethz.ch/~fukuda/cdd_home/cdd.html) of [ppl](http://bugseng.com/products/ppl)), reverse search ([lrs](http://cgm.cs.mcgill.ca/~avis/C/lrs.html)), and beneath beyond (internal). It is also possible to specify explicitly which method to use by using the `prefer_now` command.  Here we show a primal convex hull computaton, i.e., from V- to H-description, with lrs.

```perl
prefer_now "lrs";
$p = new Polytope(POINTS=>[[1,1],[1,0]]);
print $p->FACETS;
```
Output:
```
1 -1
0 1
```

Use `prefer` instead of `prefer_now` if you want to make this permanent.

## A Neighborly Cubical Polytope

`polymake` provides a variety of standard polytope constructions and transformations. This example construction introduces some of them. Check out the [documentation](https://polymake.org/doku.php/documentation/latest/polytope) for a comprehensive list.

The goal is to construct a 4-dimensional cubical polytope which has the same graph as the 5-dimensional cube. It is an example of a *neighborly cubical* polytope as constructed in


*  Joswig & Ziegler: Neighborly cubical polytopes.  Discrete Comput. Geom.  24  (2000),  no. 2-3, 325--344, [DOI 10.1007/s004540010039](http://www.springerlink.com/content/m73pqv6kr80rw4b1/)

This is the entire construction in a few lines of `polymake` code:

    


```perl
$c1 = cube(2);
$c2 = cube(2,2);
$p1x2 = product($c1,$c2);
$p2x1 = product($c2,$c1);
$nc = conv($p1x2,$p2x1);
```



Let us examine more closely what this is about. First we constructed a square `$c1` via calling the function `cube`. The only parameter `2` is the dimension of the cube to be constructed. It is not obvious how the coordinates are chosen; so let us check.

    


```perl
print $c1->VERTICES;
```
Output:
```
1 -1 -1
1 1 -1
1 -1 1
1 1 1
```


The four vertices are listed line by line in homogeneous coordinates, where the homogenizing coordinate is the leading one.  As shown the vertices correspond to the four choices of `+/-1` in two positions. So the area of this square equals four, which is verified as follows:

    


```perl
print $c1->VOLUME;
```
Output:
```
4
```


Here the volume is the Euclidean volume of the ambient space. Hence the volume of a polytope which is not full-dimensional is always zero.



The second polytope `$c2` constructed is also a square. However, the optional second parameter says that `+/-2`-coordinates are to be used rather than `+/-1` as in the default case. The optional parameter is also allowed to be `0`.  In this case a cube with `0/1`-coordinates is returned. You can access the documentation of functions by typing their name in the `polymake` shell and then hitting F1.



The third command constructs the polytope `$p1x2` as the cartesian product of the two squares. Clearly, this is a four-dimensional polytope which is combinatorially (even affinely) equivalent to a cube, but not congruent. This is easy to verify:

    


```perl
print isomorphic($p1x2,cube(4));
```
Output:
```
true
```

```perl
print congruent($p1x2,cube(4));
```
Output:
```
0
```


Both return values are boolean, represented by the numbers `1` and `0`, respectively. This questions are decided via a reduction to a graph isomorphism problem which in turn is solved via `polymake`'s interface to `nauty`.



The polytope `$p2x1` does not differ that much from the previous. In fact, the construction is twice the same, except for the ordering of the factors in the call of the function `product`. Let us compare the first vertices of the two products.  One can see how the coordinates are induced by the ordering of the factors.

    


```perl
print $p1x2->VERTICES->[0];
```
Output:
```
1 1 -1 2 2
```

```perl
print $p2x1->VERTICES->[0];
```
Output:
```
1 2 -2 1 1
```


In fact, one of these two products is obtained from the other by exchanging coordinate directions. Thats is to say, they are congruent but distinct as subsets of Euclidean 4-space. This is why taking their joint convex hull yields something interesting. Let us explore what kind of polytope we got.

    


```perl
print $nc->SIMPLE, " ", $nc->SIMPLICIAL;
```
Output:
```
false false
```


This says the polytope is neither simple nor simplicial. A good idea then is to look at the f-vector. Beware, however, this usually requires to build the entire face lattice of the polytope, which is extremely costly. Therefore this is computationally infeasible for most high-dimensional polytopes.

    


```perl
print $nc->F_VECTOR;
```
Output:
```
32 80 72 24
```


This is a first hint that our initial claim is indeed valid. The polytope constructed has 32 vertices and 80 = 32*5/2 edges, as many as the 5-dimensional cube:

    


```perl
print cube(5)->F_VECTOR;
```
Output:
```
32 80 80 40 10
```


What is left is to check whether the vertex-edge graphs of the two polytopes actually are the same, and if all proper faces are combinatorially equivalent to cubes.

    


```perl
print isomorphic($nc->GRAPH->ADJACENCY,cube(5)->GRAPH->ADJACENCY);
```
Output:
```
true
```

```perl
print $nc->CUBICAL;
```
Output:
```
true
```

See the [tutorial on graphs](apps_graph.ipynb) for more on that subject.

# Objects, Properties and Rules

### Objects
In polymake, there is two kinds of objects. A *Big Object* models a complex mathematical concept, like a Polytope or a SimplicialComplex, while a *small object* is an instance of one of the many data types commonly used in computer science, like Integers, Matrices, Sets or Maps. A big object consists of a collection of other objects (big or small) describing it, called *properties*, and functions to compute more properties from the ones already known, called *production rules*.

To get a more detailed explanation of the `polymake` object model and properties, check out the [scripting guide](https://polymake.org/doku.php/user_guide/howto/scripting#most_important_interfaces).

You can save polymake objects to disc, as explained [here](data.ipynb).

### Properties

Each (big) object has a list of properties of various types.  When an object is 'born' it comes with an initial list of properties, and all other properties will be derived from those.  Let's look at example from the `polytope` application.  The following creates a 3-dimensional cube:

```perl
$c=cube(3);
```

To find out what the initial set of properties is, use the `list_properties` method.  It returns an array of strings.  The extra code is just there to print this list nicely.

```perl
print join(", ", $c->list_properties);
```
Output:
```
CONE_AMBIENT_DIM, CONE_DIM, FACETS, AFFINE_HULL, VERTICES_IN_FACETS, BOUNDED
```

To find out the type of the object `$c`, enter

```perl
print $c->type->full_name;
```
Output:
```
Polytope<Rational>
```


To see what a property contains, use the `->` syntax:

    


```perl
print $c->FACETS;
```
Output:
```
1 1 0 0
1 -1 0 0
1 0 1 0
1 0 -1 0
1 0 0 1
1 0 0 -1
```

    
    1 1 0 0
    1 -1 0 0
    1 0 1 0
    1 0 -1 0
    1 0 0 1
    1 0 0 -1


You can also get the content of all properties using the `properties` method:

    


```perl
$c->properties;
```
Output:
```
name: c
type: Polytope<Rational>
description: cube of dimension 3


AFFINE_HULL


BOUNDED
true

CONE_AMBIENT_DIM
4

CONE_DIM
4

FACETS
1 1 0 0
1 -1 0 0
1 0 1 0
1 0 -1 0
1 0 0 1
1 0 0 -1


VERTICES_IN_FACETS
{0 2 4 6}
{1 3 5 7}
{0 1 4 5}
{2 3 6 7}
{0 1 2 3}
{4 5 6 7}
```

### Production Rules

The object is changed if we ask for a property which has not been computed before.

```perl
print $c->VERTICES;
```
Output:
```
1 -1 -1 -1
1 1 -1 -1
1 -1 1 -1
1 1 1 -1
1 -1 -1 1
1 1 -1 1
1 -1 1 1
1 1 1 1
```

```perl
print join(", ", $c->list_properties);
```
Output:
```
CONE_AMBIENT_DIM, CONE_DIM, FACETS, AFFINE_HULL, VERTICES_IN_FACETS, BOUNDED, FEASIBLE, POINTED, N_VERTICES, N_FACETS, VERTICES, LINEALITY_SPACE
```


The property `VERTICES` was added, but a few others were computed on the way, too. `polymake` applied a sequence of *production rules* that add new properties to the object that can be computed from the properties the object already posesses.

What properties *can* be computed for a given object depends on the set of rules defined for it. Here is a short sequence of commands which lets you find out.

    


```perl
$t=$c->type;
print join(", ", sorted_uniq(sort { $a cmp $b } map { keys %{$_->properties} } $t, @{$t->super}));
```
Output:
```
AFFINE_HULL, BALANCE, BALANCED, BOUNDARY_LATTICE_POINTS, BOUNDED, CANONICAL, CD_INDEX_COEFFICIENTS, CENTERED, CENTERED_ZONOTOPE, CENTRALLY_SYMMETRIC, CENTROID, CHIROTOPE, CIRCUITS, COCIRCUITS, COCIRCUIT_EQUATIONS, COCUBICAL, COCUBICALITY, COMBINATORIAL_DIM, COMPLEXITY, COMPRESSED, CONE_AMBIENT_DIM, CONE_DIM, CS_PERMUTATION, CUBICAL, CUBICALITY, CUBICAL_H_VECTOR, DEGREE_ONE_GENERATORS, DUAL_BOUNDED_H_VECTOR, DUAL_GRAPH, DUAL_H_VECTOR, EDGE_ORIENTABLE, EDGE_ORIENTATION, EHRHART_POLYNOMIAL, EHRHART_QUASI_POLYNOMIAL, EQUATIONS, EXCESS_RAY_DEGREE, EXCESS_VERTEX_DEGREE, F2_VECTOR, FACETS, FACETS_THRU_INPUT_RAYS, FACETS_THRU_POINTS, FACETS_THRU_RAYS, FACETS_THRU_VERTICES, FACET_SIZES, FACET_VERTEX_LATTICE_DISTANCES, FACET_VOLUMES, FACET_WIDTH, FACET_WIDTHS, FACE_SIMPLICITY, FAR_FACE, FAR_HYPERPLANE, FATNESS, FEASIBLE, FLAG_VECTOR, FOLDABLE_COCIRCUIT_EQUATIONS, FOLDABLE_MAX_SIGNATURE_UPPER_BOUND, FTR_CYCLIC_NORMAL, FTV_CYCLIC_NORMAL, FULL_DIM, F_VECTOR, FacetPerm, FacetPerm.pure, GALE_TRANSFORM, GALE_VERTICES, GORENSTEIN, GORENSTEIN_CONE, GORENSTEIN_INDEX, GORENSTEIN_VECTOR, GRAPH, GROEBNER_BASIS, GROUP, G_VECTOR, HASSE_DIAGRAM, HILBERT_BASIS_GENERATORS, HILBERT_SERIES, HOMOGENEOUS, H_STAR_VECTOR, H_VECTOR, INEQUALITIES, INEQUALITIES_THRU_RAYS, INEQUALITIES_THRU_VERTICES, INPUT_LINEALITY, INPUT_RAYS, INPUT_RAYS_IN_FACETS, INPUT_RAY_LABELS, INTERIOR_LATTICE_POINTS, INTERIOR_RIDGE_SIMPLICES, LATTICE, LATTICE_BASIS, LATTICE_CODEGREE, LATTICE_DEGREE, LATTICE_EMPTY, LATTICE_POINTS_GENERAT
... [output truncated]
```



Instead of showing the (lengthy) enumeration have a look at the [documentation](https://polymake.org/doku.php/documentation/latest/polytope) for a complete list of properties known for objects of the application `polytope`.


#### Schedules

You may wonder what sequence of rules led to the computation of a property you request. There usually are several mathematical ways to compute a property. `polymake` uses a nice scheduling algorithm to find the most efficient procedure, and you can look at what it returns.

Suppose we want to see which sequence of rules leads to the computation of the F_VECTOR.

    


```perl
$schedule=$c->get_schedule("F_VECTOR");
print join("\n", $schedule->list);
```
Output:
```
LINEALITY_DIM : LINEALITY_SPACE
COMBINATORIAL_DIM : CONE_DIM, LINEALITY_DIM
precondition : COMBINATORIAL_DIM ( F_VECTOR : N_FACETS, N_RAYS, COMBINATORIAL_DIM )
F_VECTOR : N_FACETS, N_RAYS, COMBINATORIAL_DIM
```

So if you ask for the f-vector, `polymake` will first compute the dimension of the lineality space from the basis of the lineality space, then compute the combinatorial dimension from the lineality and cone dimensions, and then compute the f-vector from the number of facets, number of rays, and combinatorial dimension of the polytope. Applying the schedule to the object yields the same as asking for the property right away:

```perl
$schedule->apply($c);
print join(", ", $c->list_properties);
```
Output:
```
CONE_AMBIENT_DIM, CONE_DIM, FACETS, AFFINE_HULL, VERTICES_IN_FACETS, BOUNDED, FEASIBLE, POINTED, N_VERTICES, N_FACETS, VERTICES, LINEALITY_SPACE, LINEALITY_DIM, COMBINATORIAL_DIM, F_VECTOR
```

As you can see, the things `polymake` needed to compute in order to get to the f-vector are stored in the object as well, so you don't have to recompute them later.

If you're interested, read more about rule scheduling in the [scripting guide](https://polymake.org/doku.php/user_guide/howto/scripting#rule_planning) and the article on [writing rules yourself](https://polymake.org/doku.php/user_guide/extend/rulefiles).

# Tutorial for Lattice Polytopes

This page gives a small introduction to lattice polytopes in `polymake`, some useful external software, and usage hints for it. For a list of methods and properties applicable to lattice polytopes see [here](https://polymake.org/doku.php/user_guide/lattice_polytopes_doc). For an introduction to the `polymake` package see [here](https://polymake.org/doku.php/user_guide/start). 


`polymake` always assumes that the lattice used to define a lattice polytope is the standard lattice Z<sup>d</sup>. Some rules also require that the polytope is full dimensional. There are user functions that transform a polytope sitting in some affine subspace of R<sup>d</sup> into a full dimensional polytope, either in the induced lattice or the lattice spanned by the vertices, see below. 



## Dependence on other Software

For some computations `polymake` has no built-in commands and passes the computation to external software. Currently, polymake has an interface to the following packages that compute various properties of lattice polytopes.

*  [libnormaliz](http://www.math.uos.de/normaliz/) by Winfried Bruns and Bogdan Ichim, bundled with polymake

*  [4ti2](http://www.4ti2.de/) by the 4ti2 team

*  [LattE macchiato](http://www.math.ucdavis.edu/~mkoeppe/latte/) by Matthias Köppe, building on `LattE`  by Jesus de Loera et. al.

*  ([barvinok](http://freshmeat.net/projects/barvinok) by Sven Verdoolaege)

Unless you want to deal with Hilbert bases of cones you don't need them. If you do, either the bundled extension `libnormaliz` or the external package `4ti2` suffices to do most computations with lattice polytopes. Computation of Gröbner bases currently requires `4ti2`. `LattE` only counts lattice points in a polytope and computes its Ehrhart polynomial, but may be faster on that than any other methods implemented. `barvinok` can be used to compute the number of lattice points and the  h-polynomial. Access to barvinok is realized via an extension which has to be downloaded separately.

 For some of the commands in this tutorial you will need at least one of `bundled:libnormaliz` enabled  or `4ti2` installed on your machine. We'll remind you at the relevant places.



## Lattice Points in Rational Polytopes

We start by creating a rational polytope using one of `polymake`'s standard polytope constructions. We choose the 3-dimensional cube with coordinates +1 and -1. So we start `polymake` at the command line and assign a cube to the variable $p.


```perl
$p=cube(3);
```


Suppose we want to know how many lattice points this cube contains. The answer is of course already known, as the cube has one relative interior integral point per non-empty face. So we expect to get the answer 27.

    


```perl
print $p->N_LATTICE_POINTS;
```
Output:
```
27
```

To satisfy this request, `polymake` computes all properties necessary to call an external program that provides the number of lattice points. In this case, `polymake` has passed the request to `lattE`, which is shown by the credit message that appears before the answer. By default, credits for external software are shown when an external package is used for the first time. You can change this behavior using the variable `$Verbose::credits`. If you don't have a version of `LattE`, or if you have set different preferences, then `polymake` may choose one of the other programs. So the credit statement depends on your configuration.


We can of course also ask `polymake` to compute the integral points for us. For our next computations we are only interested in the integral points in the interior of the cube, so we ask for

    


```perl
print $p->INTERIOR_LATTICE_POINTS;
```
Output:
```
1 0 0 0
```

Internally, `polymake` computes the intersection of the polytope with the integer lattice, and then checks which of the points lies on a facet of $p. By default, `polymake` uses a project-and-lift algorithms to enumerate the lattice points. Note that our call to `LattE` above has only computed the number of integral points (which is done with an improved version of Barvinok's algorithm), so `polymake` really has to compute something here. If we had asked for `INTERIOR_LATTICE_POINTS` first, then `N_LATTICE_POINTS` would just have counted the rows of a matrix, which would have been much faster. So computation time can depend on the history. 

You can also ask for the HILBERT_BASIS, though in the case of a cube the result is not so exciting: 

    


```perl
print $p->HILBERT_BASIS;
```
Output:
```
1 -1 -1 -1
1 -1 -1 0
1 -1 -1 1
1 -1 0 -1
1 -1 0 0
1 -1 0 1
1 -1 1 -1
1 -1 1 0
1 -1 1 1
1 0 -1 -1
1 0 -1 0
1 0 -1 1
1 0 0 -1
1 0 0 0
1 0 0 1
1 0 1 -1
1 0 1 0
1 0 1 1
1 1 -1 -1
1 1 -1 0
1 1 -1 1
1 1 0 -1
1 1 0 0
1 1 0 1
1 1 1 -1
1 1 1 0
1 1 1 1
```

`polymake` has no native method to compute a Hilbert basis, so it has passed the computation to `4ti2`. The choice may vary, depending on what is installed on your computer (and configured for `polymake`). You can influence the choice with the appropriate `prefer` statement. 

Note that so far these commands also work for rational polytopes. 

## Lattice Polytopes

Now we want to do some computations that don't make sense for polytopes that have non-integral vertex coordinates. We can let `polymake` check that our cube is indeed a polytope with integral vertices.

    


```perl
print $p->LATTICE;
```
Output:
```
true
```

A particularly interesting class of lattice polytopes is that of reflexive polytopes. A polytope is *reflexive* if its polar is agein alattice polytope. This implies in particular that the origin is the unique interior lattice point in the polytope. So, as we have seen above, our cube is a candidate. But this is not sufficient, so we have to do further checks.


Reflexivity is a property that is not defined for polytopes with non-integral vertices. So if we ask for it in `polymake`, then `polymake` checks that the entered polytope is indeed a lattice polytope (i.e. it is **bounded** and has **integral vertices**). In that case the object will automatically get the specialization `Polytope::Lattice`.

```perl
print $p->REFLEXIVE;
```
Output:
```
true
```

Lattice polytopes can be used to define toric varieties with an ample line bundle, and many properties of the variety are reflected by the polytope. here is an example: The toric variety defined by our cube is *smooth*, i.e. it is one of the *smooth toric Fano varieties*. In `polymake`, we can just ask for this property in the following way.

```perl
print $p->SMOOTH;
```
Output:
```
true
```


The number of integral points in the k-th dilate of a polytope is given by a polynomial of degree d in k. This is the famous *Ehrhart Theorem*. In `polymake` you can obtain the coefficients of this polynomial (starting with the constant coefficient).

    


```perl
print $p->EHRHART_POLYNOMIAL;
```
Output:
```
8*x^3 + 12*x^2 + 6*x + 1
```

`polymake` has passed this request to `LattE` or `normaliz`, but as we have used these programs already the credit message is suppressed (but if you save the cube to a file, then you will find it in there). Some coefficients of this polynomial have a geometric interpretation. E.g., the highest coefficient is the Euclidean volume of the polytope. 

    


```perl
print $p->VOLUME;
```
Output:
```
8
```

By a theorem of Stanley, the generating function for the number of lattice points can be written as the quotient of a polynomial h<sup></sup>(t) by (1-t)<sup>d+1</sup>, and this polynomial has non-negative integral coefficients. 

    


```perl
print $p->H_STAR_VECTOR;
```
Output:
```
1 23 23 1
```

```perl
print $p->LATTICE_DEGREE;
```
Output:
```
3
```

```perl
print $p->LATTICE_CODEGREE;
```
Output:
```
1
```

In our case the coefficient vector is symmetric, as the polytope is reflexive. The *co-degree* of the polytope is d+1 minus the degree of the h<sup></sup>-polynomial. It is the smallest factor by which we have to dilate the polytope to obtain an interior integral point. In our case, this is 1, as the cube already has an integral point.


We can obtain the volume of our polytope also from the `H_STAR_VECTOR`: Summing up the coefficients give the *lattice volume* of the polytope, which is d! times its Euclidean volume.

    


```perl
print $p->LATTICE_VOLUME;
```
Output:
```
48
```


Let us look at a different example: 

    


```perl
$q=new Polytope(INEQUALITIES=>[[5,-4,0,1],[-3,0,-4,1],[-2,1,0,0],[-4,4,4,-1],[0,0,1,0],[8,0,0,-1],[1,0,-1,0],[3,-1,0,0]]);
```


This actually defines a lattice polytope, which we can see from the list of vertices:

    


```perl
print $q->VERTICES;
```
Output:
```
1 3 1 7
1 2 0 3
1 3 0 7
1 2 1 7
1 2 0 4
1 3 1 8
1 3 0 8
1 2 1 8
```

`polymake` provides basically three methods for convex hull conversion, double description, reverse search, and beneath beyond. The first two are provided by the packages `cdd` and `lrs`, the last in internal. By default, `cdd` is chosen, and that is what was used above (they are bundled with `polymake`, you don't have to install them). A polytope Q is *normal* if every lattice point in the k-th dilate of Q is the sum of k lattice points in Q. You can check this property via

    


```perl
print $q->NORMAL;
```
Output:
```
false
```

So our polytope is not normal. We can also find a point that violates the condition. Being normal is equivalent to the fact, that the Hilbert basis of the cone C(Q) obtained from Q by embedding the polytope at height one and the coning over it has all its generators in height one. The property HILBERT_BASIS computes these generators:

    


```perl
print $q->HILBERT_BASIS;
```
Output:
```
1 2 0 3
1 2 0 4
1 2 1 7
1 2 1 8
1 3 0 7
1 3 0 8
1 3 1 7
1 3 1 8
2 5 1 13
```

The last row is the desired vector: [2,5,1,13] is a vector in 2*Q, but it is not a sum of lattice points in Q. The cone C(Q) corresponds to an affine toric variety, and the above tells us that this variety is not normal. Yet, it is very ample, as we can check with

    


```perl
print $q->VERY_AMPLE;
```
Output:
```
true
```

Now assume we are particularly interested in the third facet of Q. We can pick this via

    


```perl
$f=facet($q,2);
```


Recall that indexes in `polymake` start at 0, so the third facet has index 2. This is again a very ample polytope:

    


```perl
print $f->VERY_AMPLE;
```
Output:
```
true
```

The result is no surprise, being very ample is inherited by faces. We could also be interested in the facet width of the polytope `$f`. This is the minimum over the maximal distance of a facet to any other vertex. `polymake` knows how to compute this:

```perl
#print $f->FACET_WIDTH;
```

Almost. It tells you that it can only do this for a full dimensional polytope, i.e. for a polytope whose dimension coincides with the ambient dimension. This is not true for our facet: It lives in the same ambient space as `$q`, but has one dimension less. We can remedy this by applying the following:

```perl
$g=ambient_lattice_normalization($f);
print $g->FACET_WIDTH;
```
Output:
```
1
```

The function `ambient_lattice_normalization` returns a full dimensional version of the polytope `$f` in the lattice induced by the intersection of the affine space of `$f` with Z^n. Now `$g` is full dimensional, and we can compute the facet width. Note that there is also a function which normalizes in the lattice spanned by the vertices of the polytope: `vertex_facet_normalization`. This can also be usefull for full dimensional polytopes. E.g. consider the cube we defined above. The sum of the entries of each vertex is odd, so the lattice spannd by the vertices is a sublattice of the integer lattice:

    


```perl
$cr=vertex_lattice_normalization($p);
print $cr->VERTICES;
```
Output:
```
(4) (0 1)
1 1 0 0
1 0 1 0
1 1 1 0
1 0 0 1
1 1 0 1
1 0 1 1
1 1 1 1
```

`$cr` is the same cube, but we have reduced the lattice. (The first line is a *sparse representation* of a vector: it has length 4, and the only non-zero entry is at position 0 and is 1 (note that indexes start at 0)).

## Toric Varieties

`polymake` has only few builtin functions to compute properties of the variety associated to a fan or lattice polytope. There are two extensions available that add more properties, both currently at an early stage:

*  [Toric Varieties and Singular interface](https://github.com/lkastner) by Lars Kastner/Benjamin Lorenz

*  [ToricVarieties-v0.3](http://www.mathematik.tu-darmstadt.de/~paffenholz/software.html) by Andreas Paffenholz. Defines a new property for toric varieties associated to a fan and divisors on that variety. 

Here we will do some computations that do not require one of the extensions. We start by defining a fan. We'll make our live easy and take the normal fan of our cube:

    


```perl
application "fan";
```

```perl
$f = normal_fan($p);
print $f->SMOOTH_FAN;
```
Output:
```
true
```

With the last line we have verified that our fan defines a smooth toric variety. Note that switching the application is not strictly necessary, you can also prepend calls to functions and constructors with `fan::`. The fan object `$f` itself knows its type, and chooses available properties based on this. Any smooth variety is Gorenstein, so we expect the following:

    


```perl
print $f->GORENSTEIN;
```
Output:
```
true
```

Similarly, we could check for Q-Gorensteinness with `Q_GORENSTEIN`. It is also a complete fan:

    


```perl
print $f->COMPLETE;
```
Output:
```
true
```

but currently there is little support to detect completeness in `polymake`. In our case it was already decided during construction, normal fans are complete. You can also check standard features of fans, like their rays. Let us do this for the normal fan of our other example:

    


```perl
$g=normal_fan($q);
print $g->RAYS;
```
Output:
```
-1 0 1/4
0 -1 1/4
1 0 0
1 1 -1/4
0 1 0
0 0 -1
0 -1 0
-1 0 0
```

This is not what we wanted. We would like to see the minimal lattice generators of the rays. We can fix this using

    


```perl
print primitive($g->RAYS);
```
Output:
```
-4 0 1
0 -4 1
1 0 0
4 4 -1
0 1 0
0 0 -1
0 -1 0
-1 0 0
```

Note that the function `primitive` returns a copy of the argument, the RAYS as stored in the fan are unchanged. So you have to apply this function each time you need the primitive generators, or you store them in a new variable. The fan $g$ is not smooth, but still Gorenstein:

    


```perl
print $g->SMOOTH_FAN;
```
Output:
```
false
```

```perl
print $g->GORENSTEIN;
```
Output:
```
true
```

You can also access the maximal cones of the fan via

    


```perl
print $g->MAXIMAL_CONES;
```
Output:
```
{0 1 6 7}
{0 1 2 4}
{0 4 7}
{1 2 6}
{2 3 4}
{5 6 7}
{3 4 5 7}
{2 3 5 6}
```

The indices in these list refer to the list of rays. Sometimes you might be interested in the walls, i.e. the codimension 2 faces of the fan. Here is one way to get them 

    


```perl
print rows_numbered($g->HASSE_DIAGRAM->FACES);
```
Output:
```
0:-1
1:0 1 6 7
2:0 1 2 4
3:0 4 7
4:1 2 6
5:2 3 4
6:5 6 7
7:3 4 5 7
8:2 3 5 6
9:0 1
10:0 7
11:1 6
12:6 7
13:0 4
14:1 2
15:2 4
16:4 7
17:2 6
18:3 4
19:2 3
20:5 7
21:5 6
22:3 5
23:0
24:1
25:7
26:6
27:4
28:2
29:3
30:5
31:
```

```perl
print $g->HASSE_DIAGRAM->nodes_of_dim($g->DIM-2);
```
Output:
```
{23 24 25 26 27 28 29 30}
```

where the list of numbers given by the latter are the indices of the codimension 2 faces in the list of all faces given before. There is a more concise way to list those, using some simple perl programming:

    


```perl
print map($g->HASSE_DIAGRAM->FACES->[$_], @{$g->HASSE_DIAGRAM->nodes_of_dim($g->DIM-2)});
```
Output:
```
{0}{1}{7}{6}{4}{2}{3}{5}
```



## Visualization

If the lattice polytope lives in R^2 or R^3, then we can visualize the polytope together with its lattice points.



```perl
$p->VISUAL->LATTICE_COLORED;
```

The command `LATTICE_COLORED` sorted the lattice points into three classes before visualization: lattice points in the interior of the polytope, lattice points on the boundary, and vertices that are not in the lattice. These classes are then visualized with different colors (where we only see two in the above picture, as all vertices of the cube are in the lattice). If you don't need this distinction, `VISUAL->LATTICE` avoids the additional computations. 

## External Packages

`polymake` can use `4ti2` and `lattE` via a file based interface and `libnormaliz >= 3.1.0` as library, (the file based interface to `normaliz` has been discontinued) for lattice computations and prints all available packages during startup. To tell `polymake` about a newly installed program run `polymake --reconfigure` or issue the command `reconfigure` during the interactive session.  polymake may ask you to confirm the paths to the binaries.

    
    Application polytope uses following third-party software (for details: help 'credits';)
    4ti2, cddlib, latte, libnormaliz, lrslib, nauty


The output at this position depends on the software available on your computer. To see each call to an external program you can set the variable `$Verbose::external=1;`. If you just want to see the credit message instead of the program call, set `$Verbose::credits=2` instead.  If this is 1, then a credit is shown when a package is used for the first time, if 0, then all credits are suppressed (but you can find them in data files afterwards).

    

```perl
$Verbose::external=1;
```

```perl
print $p->EHRHART_POLYNOMIAL;
```
Output:
```
8*x^3 + 12*x^2 + 6*x + 1
```


You can ask `polymake` to prefer one package over another by setting `prefer "program";` where program is one of `_4ti2`, `latte` and `normaliz2`. Of course, the corresponding package needs to be installed on your computer.


To prefer one program only for some computations you may append one of .integer_points, .hilbert, .ehrhartpoly for rules computing N_LATTICE_POINTS, LATTICE_POINTS, HILBERT_BASIS or EHRHART_POLYNOMIAL. (Or `prefer_now` just for the next computation)

    


```perl
print cube(2)->N_LATTICE_POINTS;
```
Output:
```
9
```

```perl
prefer_now "libnormaliz";
print cube(2)->N_LATTICE_POINTS;
```
Output:
```
9
```

```perl
print cube(2)->EHRHART_POLYNOMIAL;
```
Output:
```
4*x^2 + 4*x + 1
```

# Scripting

From the technical point of view, there is no difference between
commands you enter in the interactive session and the scripts: in both
may any valid perl expression is accepted. The difference lies more in
the psychology: while for simple interactive commands practically no
knowledge in programming is needed, the scripting requires certain
profoundness in the perl language.

But please don't be scared: even with minimal programming skills you can
save a lot of time and typing. The very first scripting exercise can
just consist of copying some lines from the interactive history buffer
(available by invoking `history;` command or directly from the file
`~/.polymake/history`) into a separate script file. As you better get
acquainted with perl and your programming experience grows, you'll be
able to realize more and more complex ideas.

This page is not aimed, however, as an introduction in the perl
language. There is a lot of excellent literature available on this
topic, and even the man pages, otherwise notorious for their
ineligibility for novices, are very instructive and rich in explanatory
examples. Here you'll rather found details which are special to the
polymake's “dialect” of perl.

## Calling

A script can be called from the interactive polymake shell or from other
scripts via the special function `script`:

``` code
script("scriptfile", arg1, ...);
```

As arguments any valid perl expressions may be passed. Alternatively, a
script may be executed directly from the UNIX command line:

``` code
polymake --script scriptfile ARG1 ARG2
```

Here you can only pass strings (like file names) or numeric constants as
arguments. Besides this restriction, you should keep in mind that if you
execute a script in this fashion, the readline library isn't loaded at
all, thus you won't be able to take any interactive actions like
importing extensions or reconfiguring some rules. Normally you will
hardly ever do it in your scripts, but should you need some interaction
in some exotic case, just change the option from `--script` to
`--iscript` .

## Structure

A script can contain pretty anything allowed by perl syntax rules.
However, to get access to polymake classes and functions, it needs a
preamble:

``` code
use application "NAME";
```

It sets a default application for the rest of the enclosing lexical
context (that is, normally, up to the next `use application` statement
or the end of the script file, but may also be just the enclosing
block). The notion of the default application has exactly the same
meaning as the [current
application](//polymake.org/doku.php/shell#switching_applications "shell")
for the interactive shell: Functions and class names defined in or
imported into the default application may be used without qualification,
while names from other applications must be prefixed by the application
name.

The script code is compiled in the package `Polymake::User`, the same as
the interactive shell expressions are evaluated in. Thus the scripts can
access non-local variables introduced in the shell and vice versa,
having run the script once, you can use the variables and subroutines
defined in the script. If you want to define additional packages, please
define them as subpackages of `Polymake::User` or completely outside
`Polymake::`, to prevent accidental clashes with polymake internal
classes.

The script may define subroutines and/or contain file-level code. The
latter is assembled together to a anonymous subroutine which is executed
each time you call the `script` function; its return value is the last
expression executed in the file-level code (or in a `return` statement,
if any). The arguments are passed in the global array `@ARGV`, not in
`@_` as for usual subroutines. If you intend to use your script in both
interactive and batch mode, you might want to build in some flexible
recognition of argument types, for example, allowing for both ready
objects and filenames to be passed:

``` code
  my $p=shift @ARGV;
  $p=load($p) unless is_object($p);
```

Since the script code may be repeatedly executed arbitrarily many times,
you should put a special attention to variables requiring one-time
initialization. Such initializations should be either put in a `BEGIN`
block or guarded by `||=` or `//=` operators. Also please note that if
you introduce `my` variables on a file level and define other
subroutines in the script which refer to these variables, the
subroutines capture the values assigned during the first execution of
the script. Even if your script changes the values of these `my`
variables during each execution, the captured values in the subroutines
will remain unaffected. (It'll be of no surprise for seasoned perl
hackers familiar with the notion of *closures*).

You can modify the script file in a text editor without leaving the
polymake session. The `script` function stores the timestamps of all
executed script files, so the changes will be detected by the next call
to `script` and the script file will be reloaded automatically.

## Location

Scripts can be kept in arbitrary folders. Unless the script you want to
execute resides in the current directory, you must specify its full path
in the `script` command. TAB completion assists you at this. There are,
however, special locations, where the scripts are found just by name.
Moreover, some locations impose special semantics on the scripts.

Neutral scripts, that is, those capable of working with arbitrary
applications, and scripts explicitly switching the applications, can be
kept at the following places:

- `$InstallTop/scripts` – standard neutral scripts shipped with polymake

- `@lookup_scripts` – additional directories of your choice containing
  your private scripts. This list is a [custom
  variable](//polymake.org/doku.php/user_guide/howto/shell_custom#custom_variables "user_guide:howto:shell_custom").

- `$Extension/scripts` – neutral scripts coming from an
  [extension](//polymake.org/doku.php/user_guide/extend/extensions "user_guide:extend:extensions")

Application-specific scripts are kept in the applications' subtrees:

- `$InstallTop/apps/APPNAME/scripts` – standard scripts shipped with
  polymake

- ` $Extension/apps/APPNAME/scripts` – scripts coming from an extension

These scripts don't need the preamble `use application`, it is
automatically imposed. An application-specific script can be executed
with the `script` command if its application is the current one or is
imported by the current application.

Your collection of scripts will probably grow over the time, some
scripts sharing common code parts. The common code is usually extracted
in separate `.pl` or `.pm` files included with `require` statement. The
lookup rules for these files is a bit different: the directories to be
searched have to be inserted into the global array `@INC`. The
appropriate `push` or `unshift` statements can be placed in your
personal startup script `~/.polymake/init.pl`. We recommend, however, to
create a private extension and store the scripts and the included files
in subdirectories `scripts` and `perllib` respectively. In this setting
you don't have to manipulate any lookup list.

