<!-- Vendored from https://www.cs.unm.edu/~mccune/prover9/manual/2009-11A/ (Prover9/Mace4 manual, version 2009-11A): pages intro, running, input, syntax, goals, options, auto, output, mace4, m4-input, m4-options, m4-interpformat, prooftrans; converted to markdown -->


------------------------------------------------------------------------

*Prover9 Manual*


*Version 2009-11A*

------------------------------------------------------------------------

# Introduction

[Prover9](http://www.cs.unm.edu/~mccune/prover9/) is a
resolution/paramodulation automated theorem prover for first-order and
equational logic. Prover9 is a successor of the
[Otter](http://www.cs.unm.edu/~mccune/otter/) Prover
\[[McCune-Otter33](references.html#McCune-Otter33)\].

## Getting Started

Prover9 has a fully [automatic mode](auto.html) in which the user simply
gives it formulas representing the problem. See the Section [Clauses and
Formulas](syntax.html).

An good way to learn about Prover9 is to browse and study the [example
input and output
files](http://www.cs.unm.edu/~mccune/prover9/examples/). *Users are
encouraged to contribute examples from their own work with Prover9 (and
Mace4).*

## Related Programs

Several programs come bundled with Prover9. The most important is
[Mace4](mace4.html), which looks for finite models and counterexamples.
Mace4 can help avoid wasting time searching for a proof with Prover9 by
first finding a counterexample or by first helping to debug logical
specifications.

Another useful program is [Prooftrans](prooftrans.html), which can
transform proofs found by Prover9 in various ways, including producing
more detailed proofs, simplifying the justifications, renumbering the
steps, producing proofs in XML, and producing proofs for input to other
programs.

## Terms of Use

Prover9, Mace4, related programs, and the LADR libraries (with which
they were all constructed) are distributed under the terms of the [**GNU
General Public License (v2)**](http://www.gnu.org/copyleft/gpl.html).

## Other Theorem Provers

- [E](http://www.eprover.org) is a very good all-around prover.
- [Waldmeister](http://www.mpi-sb.mpg.de/~hillen/waldmeister/) is a fast
  prover for equational logic.
- [Vampire](http://en.wikipedia.org/wiki/Vampire_theorem_prover) has
  lately been winning the MIX category of
  [CASC](http://www.cs.miami.edu/~tptp/CASC/).
- [Paradox](http://www.cs.chalmers.se/~koen/paradox/) is an excellent
  program for finding finite models and counterexamples.
- See the [CASC Website](http://www.cs.miami.edu/~tptp/CASC/) for
  information on lots of other good provers.

## Format Conventions for this Manual

Many parts of this manual are displayed in boxes with different
background colors.

A display like the following indicates part of an input or output file.

``` my_file
formulas(sos).
  all x all y (subset(x,y) <-> (all z (member(z,x) -> member(z,y)))).
end_of_list.

formulas(goals).
  all x all y all z (subset(x,y) & subset(y,z) -> subset(x,z)).
end_of_list.
```

A display like the following indicates a job that is run on a command
line, for example, a command to run a Prover9 job.

``` my_job
prover9 -f subset_trans.in > subset_trans.out
```

A display like the following indicates some output that appears on the
computer screen, for example, a message from Prover9.

``` my_screen
-------- Proof 1 --------
THEOREM PROVED
------ process 3666 exit (max_proofs) ------
```

Displays like the following contain algorithms.

``` my_code
Simplify clause (c):
    demodulate c
    merge identical literals
```

A display like the following notes an important difference between
Prover9 and Otter.

> Prover9's automatic mode is set by default. Otter's automatic mode
> must be explicitly set.

------------------------------------------------------------------------

Next Section: [Installation](install.html)


------------------------------------------------------------------------

*Prover9 Manual*


*Version 2009-11A*

------------------------------------------------------------------------

# Running Prover9

The standard way of running Prover9 is to (1) prepare an input file
containing the logical specification of a conjecture and the search
parameters, (2) issue a command that runs Prover9 on the input file and
produces an output file, (3) look at the output, and (4) maybe run
Prover9 again with different search parameters.

A [graphical user interface (GUI) for
Prover9](http://www.cs.unm.edu/~mccune/prover9/gui/) is under
development, but it is not described in this manual. Nearly all of the
information in this manual applies also when using the GUI.

## An Input File

Here is an input file; assume it is named `subset_trans.in`.
(Use a plain text editor, not a word processor, to create input files.)

``` my_file
formulas(sos).
  all x all y (subset(x,y) <-> (all z (member(z,x) -> member(z,y)))).
end_of_list.

formulas(goals).
  all x all y all z (subset(x,y) & subset(y,z) -> subset(x,z)).
end_of_list.
```

## A Basic Prover9 Command

Here is a command to run Prover9 on the preceding file and send the
output to a file called `subset_trans.out`.

``` my_job
prover9 -f subset_trans.in > subset_trans.out
```

When you run the preceding command, a message like the following should
appear immediately on your screen.

``` my_screen
-------- Proof 1 --------
THEOREM PROVED
------ process 3666 exit (max_proofs) ------
```

The output file [subset_trans.out](subset_trans.out) should contain the
proof (and a lot of other information about the job).

## Taking Input from Standard Input

Prover9 jobs can be run in a slightly different way, taking input from
"standard input" instead of a named file, as follows.

``` my_job
prover9 < subset_trans.in > subset_trans.out2
```

The disadvantage of using this method is that the name of the input file
is not given in the output file.

## More Than One Input File

The input can occur in more than one file:

``` my_job
prover9 -f subset.in trans.in > subset_trans.out3
```

All arguments after the "`-f`" are taken as input filenames, and there
can be as many as you like. When multiple filnames are given on the
command line, a list of objects (clauses, formulas, or terms) cannot be
split across more than one file.

## Time Limit on the Command Line

Prover9 also accepts a time limit, in seconds, on the command line. The
following command limits the job to about 10 seconds.

``` my_job
prover9 -t 10 -f subset_trans.in > subset_trans.out4
```

If "`-t`" and "`-f`" are both in the command, the "`-t`" must occur
first.

## Getting Statistics During the Search

*This section applies to Unix-like systems only.*

If a Prover9 process is running in the background, one can tell it to
send search statistics (without killing the job) to the output file
sending a "USR1" signal to the process. For example,

``` my_job
% prover9 -f p3a.in > p3a.outb &
    [1] 31613
% kill -USR1 31613
    A report (17.75 seconds) has been sent to the output.
```

## Calling Prover9 From Another Program

If Prover9 is called from another program (e.g., a shell script, a Perl
script, or a Python script), Prover9's exit codes can tell the other
program the reason Prover9 terminates. The following table shows the
exit codes.

Exit Code

Reason for Termination

0 (MAX_PROOFS)

The specified number of proofs
([**`max_proofs`**](limits.html#max_proofs)) was found.

1 (FATAL)

A fatal error occurred (user's syntax error or Prover9's bug).

2 (SOS_EMPTY)

Prover9 ran out of things to do (sos list exhausted).

3 (MAX_MEGS)

The [**`max_megs`**](limits.html#max_megs) (memory limit) parameter was
exceeded.

4 (MAX_SECONDS)

The [**`max_seconds`**](limits.html#max_seconds) parameter was exceeded.

5 (MAX_GIVEN)

The [**`max_given`**](limits.html#max_given) parameter was exceeded.

6 (MAX_KEPT)

The [**`max_kept`**](limits.html#max_kept) parameter was exceeded.

7 (ACTION)

A Prover9 [action](actions.html) terminated the search.

101 (SIGINT)

Prover9 received an interrupt signal.

102 (SIGSEGV)

Prover9 crashed, most probably due to a bug.

The calling program will probably want to look in Prover9's output, for
example, to extract a proof. See the page on [Prover9 output
files](output.html).

------------------------------------------------------------------------

Next Section: [Input Files](input.html)


------------------------------------------------------------------------

*Prover9 Manual*


*Version 2009-11A*

------------------------------------------------------------------------

# Prover9 Input Files

Prover9 takes its input from one or more (usually one) files. If there
is more than one input file, lists of objects (formulas, weighting
rules, etc.) cannot be split across more than one file. The page
[Running Prover9](running.html) shows how to specify the files in the
commands to run Prover9.

## Comments and Whitespace

There are two kinds of comment:

- *Line comment*. If the first '`%`' (percent sign) on a line is not the
  start of a block comment ('`%BEGIN`'), everything from that symbol
  through the end of the line is ignored.
- *Block comment*. If the parser sees the string '`%BEGIN`', that is not
  in a line comment, it will ignore everything up through the next
  occurrence of '`END%`'. Line breaks are irrelevant. If there is no
  '`END%`', the rest of the file is ignored, without causing an error.

Comments are not echoed to the output file. Clauses can have [label
attributes](attributes.html) which can serve as different kind of
comment which *does* appear in the output file.

Whitespace (spaces, newlines, tabs, etc.) is optional in most places.
The important exception is that whitespace is required around some
operations in clauses and formulas (see the page [Clauses and
Formulas](syntax.html)).

## A Simple Example

The most basic kind of input file consists of list of
[clauses](glossary.html#clause) named "`sos`" representing the negation
of the conjecture, as in the following example.

``` my_file
formulas(sos).           % clauses to be placed in the sos list
  -man(x) | mortal(x).
  man(george).
  -mortal(george).
end_of_list.
```

Prover9 will take the clauses, use its automatic mode to decide on the
inference rules, and then search for a refutation.

The preceding example can also be stated in a more natural way by using
a non-clausal formula for the man-implies-mortal rule and the [`goals`
list](goals.html) for the conclusion, as follows.

``` my_file
formulas(assumptions).   % synonym for formulas(sos).
  man(x) -> mortal(x).   % open formula with free variable x
  man(george).
end_of_list.

formulas(goals).         % to be negated and placed in the sos list
  mortal(george).
end_of_list.
```

Prover9 will transform the formulas in this input to the same clauses as
in the basic input above before starting the search for a refutation.

> In Otter and in earlier versions of Prover9, "clauses" and "formulas"
> were distinct types of object, and formulas could not have free
> variables. Now, clauses are a subset of formulas, and Prover9 decides
> which formulas are non-clausal and takes the appropriate actions to
> transform them to clauses.

## Types of Input

Prover9 input consists of lists of objects (formulas or terms) and
commands.

### Lists of Objects

Lists of objects start with a type (`formulas` or `terms`) and name
(`sos`, `goals`, `weights`, etc.), and end with `end_of_list`. The
following display show an example of each type of accepted list, with
one object in each list.

``` my_file
formulas(sos).           p(x).     end_of_list.   % the primary input list
formulas(assumptions).   p(x).     end_of_list.   % synonym for formulas(sos)
formulas(goals).         p(x).     end_of_list.   % some restrictions (see Goals)
formulas(usable).        p(x).     end_of_list.   % seldom used
formulas(demodulators).  f(x)=x.   end_of_list.   % seldom used, must be equalities
formulas(hints).         p(x).     end_of_list.   % should be used more often  (see Hints)

list(weights).         weight(a) = 10.                         end_of_list. % see Weighting
list(kbo_weights).     a = 3.                                  end_of_list. % see Term Ordering
list(actions).         given = 100 -> set(print_kept).         end_of_list. % see Actions
list(interpretations). interpretation(2,[],[relation(p,[1])]). end_of_list. % see Semantics
```

If the input contains more than one list of a particular type/name, the
lists are simply concatenated by Prover9 as they are read.

### Commands

Eleven types of command are accepted. Here is an example of each.

``` my_file
op(400, infix_right, ["+", "--"]). % declare parse precedence and type (see Clauses and Formulas)

redeclare(negation, "~"]).         % change the negation symbol (see Clauses and Formulas)

set(print_kept).                   % set a flag

clear(auto_inference).             % clear a flag

assign(max_weight, 40).            % integer parameter

assign(stats, some).               % string parameter

assoc_comm(*).                     % not currently used for Prover9

commutative(g).                    % not currently used for Prover9

predicate_order([=,<=,P,Q).        % predicate symbol precedence (see Term Ordering)

function_order([0,1,a,b,f,g,*,+]). % function symbol precedence (see Term Ordering)

lex([0,1,a,b,f,g,*,+]).            % synonym for "function_order"

skolem([a,b,f,g]).                 % declare symbols to be Skolem functions (rarely used)
```

## Order of Commands and Lists of Objects

For the most part, the order of things in the input file(s) is
irrelevant. For example, commands can usually be mixed with lists of
objects. The situations in which order matters are listed here.

- The `op(precedence, type, symbols)` commands must occur before any
  clauses or formulas that contain the affected symbols.
- Some of the flags and parameters alter other flags and parameters. The
  alterations can be undone by placing the appropriate command after the
  command that alters. The output file clearly shows what happens in
  these cases.

Note that changing the order of clauses or formulas within a list,
changing the order of literals in a clause, or changing the order of
subformulas in a formula can change the search, occasionally in
substantial ways.

## Conditional Inclusion

Many input files can be used for multiple programs (e.g., Prover9 and
Mace4). The following construct says to include the enclosed input for
the given program only.

``` my_file
if(program-name).
   ... conditionally-included input ...
end_if.
```

For example, to specify that Mace4 and Prover9 have different time
limits, one can write

``` my_file
if(Mace4).
  assign(max_seconds, 30).
end_if.

if(Prover9).
  assign(max_seconds, 3600).
end_if.
```

The conditional-inclusion construct cannot occur within a list of
objects (formulas, weighting rules, etc.).

------------------------------------------------------------------------

Next Section: [Clauses & Formulas](syntax.html)


------------------------------------------------------------------------

*Prover9 Manual*


*Version 2009-11A*

------------------------------------------------------------------------

# Clauses and Formulas

The [Glossary Page](glossary.html) contains definitions of
[term](glossary.html#term), [atomic
formula](glossary.html#atomic%20formula),
[literal](glossary.html#literal), [clause](glossary.html#clause), and
[formula](glossary.html#formula) from a logical point of view. This page
contains descriptions of how those kinds of things are parsed and
printed, and we refer to them collectively as *objects*.

> In Otter and in earlier versions of Prover9, "clauses" and "formulas"
> were distinct types of object, and "formulas" could not have free
> variables. Now, clauses are a subset of formulas.

Here are the important points about clauses and formulas.

- Clauses are a subset of formulas. All input formulas, including
  clauses, appear in a list headed by `formulas(`*`list_name`*`)`.
- There is a rule for distinguishing variables from constants, because
  clauses and other formulas can have free variables (variables not
  bound by quantifiers). The default rule is that variables start with
  (lower case) `u` through `z`. For example, in the formula `P(a,x)`,
  the term `a` is a constant, and `x` is a variable. (See also the flag
  [**`prolog_style_variables`**](syntax.html#prolog_style_variables).)
- Free variables in clauses and formulas are assumed to be universally
  quantified at the outermost level.
- Prover9's inference rules operate on clauses. If non-clausal formulas
  are input, Prover9 immediately translates them clauses by
  [NNF](glossary.html#NNF),
  [Skolemization](glossary.html#skolemization), and
  [CNF](glossary.html#CNF) conversions.

## Parsing and Printing Objects

The *prefix standard form* of an object with an n-ary symbol, say `f`,
at the root is

``` my_file
f( argument_1, ..., argument_n )
```

Whitespace (spaces, tabs, newline, etc.) is accepted anywhere except
within symbols.

Prover9 will accept any term or formula written prefix standard form.
However formulas and many terms can be written in more convenient ways,
for example, "`a=b | a!=c'`" instead of "`|(=(a,b),-(=(a,'(c))))`".

Prover9 uses a general mechanism in which binary and unary symbols can
have special parsing properties such as "infix",
"infix-right-associated", "postfix". In addition, each of those symbols
has a precedence so that many parentheses can be omitted. (The mechanism
is similar to those used by most Prolog systems.)

Many symbols have built-in parsing properties (see the [table
below](#built_in)), and the user can declare parsing properties for
other symbols with the "op" command.

Clauses and formulas make extensive use of the built-in parsing
properties for the equality relation and the logic connectives. Instead
of first presenting the general mechanism, we will present the syntax
for formulas under the assumption of the built-in parsing properties.
The general mechanism is described below in the section [Infix, Prefix,
and Postfix Declarations](#declarations).

### Symbols

Symbols include variables, constants, function symbols, predicate
symbols, logic connectives. Symbols do not include parentheses or
commas.

Prover9 recognizes several kinds of symbol.

- An *ordinary symbol* is a (maximal) string made from the characters
  `a`-`z`, `A`-`Z`, `0`-`9`, `$`, and `_`.
- A *special symbol* is a (maximal) string made from the *special
  characters*: `` {+-*/\^<>=`~?@&|!#';} ``.
- A *quoted symbol* is any string enclosed in double quotes.
- The *empty list symbol* is `[]`. This is a special case.

The reason for separating ordinary and special symbols is so that
strings like `a+b`; that is, `+(a,b)`, can be written without any
whitespace around the `+`.

A symbol cannot have both ordinary and special characters, for example
`R+` (unless it is a quoted symbol).

Objects (terms or formulas) are constructed from symbols, parentheses,
and commas.

### Overloaded Symbols

In most cases, symbol overloading is not allowed. For example a symbol
cannot be both a function symbol and a predicate symbol, or both a
constant and a binary function symbol. There are a few exceptions.

- The logic connectives can also be used as function or predicate
  symbols of the same arity. For example, `-` is typically used as unary
  arithmetic minus well as for logical negation.

> Prover9 is much more strict about overloading symbols than Otter is.

### Symbols With Meaning

Several symbols have built-in meaning. These are the equality symbols
(`=`, `!=`) and logic connectives (`-`, `|`, `&`, `->`, `<-`, `<->`,
`all`, `exists`). These symbols can be changed as described in the
section [Redeclaring Built-in Symbols](#redeclare). (Parentheses, comma,
period, and the list construction symbols cannot be redeclared.)

Terms

Any term can be written in prefix standard form, for example,
`f(g(x),y)` and `*('(x),y)`. If symbols in the term have
parsing/printing properties (either [built-in](#built_in)) or declared
with the `op` command), the term can be written in infix/prefix/postfix
form with assumed precedence, for example, `x'*y`, which represents
`*('(x),y)` under the built-in parsing/printing properties.

A list notation similar to Prolog's can be used to write terms that
represent lists. Note that the "cons" operator is "`:`", instead of
"`|`" as in Prolog.

Term

Standard Prefix Form

What it Is

`[]`

`$nil`

the empty list

`[a,b,c]`

`$cons(a,$cons(b,$cons(c,$nil)))`

list of three objects

`[a:b]`

`$cons(a,b)`

first, rest

`[a,b:c]`

`$cons(a,$cons(b,c))`

first, second, rest

Lists are frequently used in Prover9 commands such as the
[`function_order`](input.html#lists) command, and they are sometimes
also used in clauses and formulas.

### Atomic Formulas

Equality is a built-in special case. The binary predicate symbol `=` is
usually written as an infix relation. The binary symbol `!=` is an
abbreviation for "not equal"; that is, the formula `a!=b` stands for
`-(a=b)`, or more precisely, `-(=(a,b))`. From the semantics point of
view, the binary predicate symbol `=` is the one and only equality
symbol for the inference rules that use equality.

### Clauses

The disjunction (OR) symbol is `|`, and the negation (NOT) symbol is
`-`. The disjunction symbol has higher precedence than the equality
symbol, so equations in clauses do not need parentheses. Every clause
ends with a period. Examples of clauses follow (Prover9 adds some extra
space when printing clauses).

``` my_file
formulas(sos).
    p|-q|r.
    a=b|c!=d.
    f(x)!=f(y)|x=y.
end_of_list.
```

### Formulas

Meaning

Connective

Example

negation

`-`

`(-p)`

disjunction

`|`

`(p | q | r)`

conjunction

`&`

`(p & q & r)`

implication

`->`

`(p -> q)`

backward implication

`<-`

`(p <- q)`

equivalence

`<->`

`(p <-> q)`

universal quantification

`all`

`(all x all y p(x,y))`

existential quantification

`exists`

`(exists x exists y p(x,y))`

When writing formulas, the [built-in parsing declarations](#built_in)
allow many parentheses to be omitted. For example, the following two
formulas are really the same formula.

``` my_file
formulas(sos).
 all x  all y (p <->   -q  |  r &  -s)     .
(all x (all y (p <-> ((-q) | (r & (-s)))))).
end_of_list.
```

> For Prover9 formulas, each quantified variable must have its own
> quantifier; Otter allows quantifiers to be omitted in a sequence of
> quantified variables with the same quantifier. For example, Otter
> allows `(all x y z p(x,y,z))`, and Prover9 requires
> `(all x all y all z p(x,y,z))`.

Infix, Prefix, and Postfix Declarations

Several symbols are understood by Prover9 as having special parsing
properties that determine how terms involving those symbols can be
arranged. In addition, the user can declare additional symbols to have
special parsing properties.

### Parsing Declarations

The "op" command is used to declare parse types and precedences.

``` my_file
op( precedence, type, symbols(s) ).  % declare parse type and precedence
```

- 1 ≤ *`precedence`* ≤ 998.
- *`type`* is one of {
  `infix, infix_left, infix_right, prefix, prefix_paren, postfix, postfix_paren, ordinary`
  }.
- *`symbol(s)`* is either a symbol or a list of symbols. Each
  multi-character special symbol must be enclosed in double quotes.

> Prover9 does not allow different symbol types with the same
> precedence, for example,
>
> ``` my_file
> op(325, postfix, ').
> op(325, prefix, ~).
> ```
>
> This restriction prevents ambiguous strings such as `~x'`.

The following table shows an example of each type of parsing property
(and ignores precedence).

Type

Example

Standard Prefix

Comment

`infix`

`a*(b*c) `

`*(a,*(b,c))`

like Prolog's `xfx`

`infix_left`

`a*b*c `

`*(*(a,b),c)`

like Prolog's `yfx`

`infix_right`

`a*b*c `

`*(a,*(b,c))`

like Prolog's `xfy`

`prefix`

`--p `

`-(-(p)) `

like Prolog's `fy`

`prefix_paren`

`-(-p) `

`-(-(p)) `

like Prolog's `fx`

`postfix`

`a'' `

`'('(a)) `

like Prolog's `yf`

`postfix_paren`

`(a')' `

`'('(a)) `

like Prolog's `xf`

`ordinary`

`*(a,b) `

`*(a,b) `

takes away parsing properties

Higher precedence means closer to the root of the object, and lower
precedence means the the symbol binds more closely. For example, assume
that the following declarations are in effect.

``` my_file
op(790, infix_right,  "|" ).  % disjunction in formulas or clauses
op(780, infix_right,  "&" ).  % conjunction in formulas
```

Then the string `a & b | c` is an abbreviation for `(a & b) | c`.

The built-in parsing declarations are shown in the following box. The
ones with comments have built-in meanings; the others are for general
use as function or predicate symbols.

``` my_file
op(810, infix_right,  "#" ).  % for attaching attributes to clauses

op(800, infix,      "<->" ).  % equivalence in formulas
op(800, infix,       "->" ).  % implication in formulas
op(800, infix,       "<-" ).  % backward implication in formulas
op(790, infix_right,  "|" ).  % disjunction in formulas or clauses
op(780, infix_right,  "&" ).  % conjunction in formulas

% Quantifiers (a special case) have precedence 750.

op(700, infix,        "=" ).  % equal in atomic formulas
op(700, infix,       "!=" ).  % not equal in atomic formulas
op(700, infix,       "==" ).
op(700, infix,        "<" ).
op(700, infix,       "<=" ).
op(700, infix,        ">" ).
op(700, infix,       ">=" ).

op(500, infix,        "+" ).
op(500, infix,        "*" ).
op(500, infix,        "@" ).
op(500, infix,        "/" ).
op(500, infix,        "\" ).
op(500, infix,        "^" ).
op(500, infix,        "v" ).

op(350, prefix,       "-" ).  % logical negation in formulas or clauses
op(300, postfix,      "'" ).
```

The built-in parsing declarations can be overridden with ordinary "op"
commands. Be careful, however, when overriding parsing declarations for
symbols with built-in meanings. For example, say you wish to use "#" as
an infix function symbol and give the following the declaration.

``` my_file
op(500, infix, "#").
```

Then clauses with attributes might have be written with more
parentheses, for example, as

``` my_file
(p(a) | q(a)) # (label(a) # label(b)).
```

If you wish to use one of the symbols with built-in parsing declarations
as an ordinary prefix symbol, you can undo the declaration by giving an
"op" command with type "ordinary". The following example clears the
parse types for two symbols.

``` my_file
op(ordinary, ["*","+"]).   % there is no precedence argument for type "ordinary"
```

Finally, the following example shows that parsing declarations can be
changed anywhere in the input, with immediate effect. This can be useful
for example, if lists of clauses come from different sources.

``` my_file
op(400,infix_left,"*").  % assume left association for following clauses

formulas(sos).
  P(a * b * c).
end_of_list.

op(400,infix_right,"*"). % assume right association for following clauses

formulas(sos).
  Q(d * e * f).
end_of_list.

op(400,infix,"*").  % from here on, include all parentheses (input and output)
```

An excerpt from the output of the preceding example shows how the
clauses are printed after the last "op" command.

``` my_file
formulas(sos).
P((a * b) * c).  [assumption].
Q(d * (e * f)).  [assumption].
end_of_list.
```

## Prolog-Style Variables

``` my_option
set(prolog_style_variables).
clear(prolog_style_variables).    % default clear
```

> A rule is needed for distinguishing variables from constants in
> clauses and formulas with free variables. If this flag is clear,
> variables in clauses start with (lower case) 'u' through 'z'. If this
> flag is set, variables in clauses start with (upper case) 'A' through
> 'Z'.
>
> Prover9 decides whether symbols are constants or variables after it
> has read all of its input, so the state of the flag
> [**`prolog_style_variables`**](syntax.html#prolog_style_variables) at
> the end of the input determines the rule that is used for *all*
> formulas. For example, in the following input,
>
> ``` my_file
> formulas(sos).
>   p(x,A).
> end_of_list.
>
> set(prolog_style_variables).
>
> formulas(sos).
>   q(y,B).
> end_of_list.
> ```
>
> the term `x` is a constant, and `A` is a variable.

Redeclaring Built-in Symbols

NOTE: Keep in mind the difference between *semantic* properties of
symbols (e.g., logic connectives) and *parsing/printing* properties of
symbols (e.g., infix with high precedence). Those two kinds of property
are independent (by default, many symbols have both).

Most of the symbols with built-in meaning can be changed to other
symbols. The symbols that can be changed are shown in the following
table.

Operation

Default Symbol

true

`$T`

false

`$F`

negation

`-`

disjunction

`|`

conjunction

`&`

implication

`->`

backward_implication

`<-`

equivalence

`<->`

universal_quantification

`all`

existential_quantification

`exists`

equality

`=`

negated_equality

`!=`

attribute

`#`

To change the symbol associated with an operation, one uses the
following command.

``` my_file
redeclare( operation, symbol ).  % associate a different symbol with an operation
```

For example, the following command says that "`AND`" will be used for
conjunction.

``` my_file
redeclare(conjunction, AND).  % change the conjunction symbol to AND.
```

As with the "`op`" command, if the new symbol is a multicharacter
[special symbol](#special_symbol), it must be enclosed in double quotes,
as in the following example.

``` my_file
redeclare(conjunction, "&&").  % change the conjunction symbol to &&.
```

When in doubt, quote the symbol, because unnecessary quotes are ignored
in the "`redeclare`" and "`op`" commands.

### Parsing/Printing Properties and Redeclarations

Many of the default symbols for the built-in operations have default
printing/parsing properties, for example, the default properties for
default conjunction symbol are

``` my_file
op(780, infix_right,  "&" ).  % conjunction in formulas
```

When a redeclaration for such an operation occurs, the parsing/printing
properties are copied from the old symbol to the new symbol. For
example, when conjunction is changed to `AND`, the following is
*automatically* applied.

``` my_file
op(780, infix_right,  AND ).
```

If the user wishes some other printing/parsing properties for the new
symbol, the appropriate "`op`" command can be placed after the
"`redeclare`" command.

### Redeclaration Example

The following example shows redeclarations of many of the operations.

``` my_job
prover9 -f redeclare.in > redeclare.out
```

### Location of Redeclare Commands

Most of the operations can be redeclared repeatedly throughout the
input. The declarations in effect when a formula is read will be used,
ane the ones in effect at the end of the input will be used for all
subsequent output.

*An exception*: If the operations "`equality`" or "`negated_equality`"
are redeclared, it must be done before any formulas containing those
symbols are read.

------------------------------------------------------------------------

Next Section: [Auto Modes](auto.html)


------------------------------------------------------------------------

*Prover9 Manual*


*Version 2009-11A*

------------------------------------------------------------------------

# Goals and Denials

This section shows how the conclusion(s) of a conjecture can be stated
in positive form, how one can search for direct proofs as opposed to
bidirectional proofs, and how multiple conclusions are stated and
handled.

Terminology

- *Conclusion*: this term is used informally.
- *Goal*: this term refers to a conclusion stated in positive form.
- *Denial clause*: this term refers to a negative clause in a [Horn
  set](glossary.html#horn), because such clauses usually correspond to
  the negation of a conclusion.

## Goals: Stating Conclusions in Positive Form

> In Otter, the conclusions are always stated in negated form.

Prover9 allows the user to state conclusions in positive form by using
the list `formulas(goals)`. However, Prover9 always works by refutation,
so the clauses or formulas in the `goals` lists are negated as described
below, and the results are appended to the `sos` clause list before the
search starts. In other words, goals are "syntactic sugar" for input,
and have nothing to do with the way Prover9 conducts its search for
refutations.

When the conclusion is given in positive form, the user has no control
over the [Skolem](glossary.html#skolemization) symbols (if any) that
Prover9 introduces. If the user needs some control of the Skolem
symbols, for example, to insert them into the symbol precedence at a
particular spot, or to include them in the weighting function, the user
should do the Skolemizing and give the conclusion in negated form.

If there is just one formula in `formulas(goals)`, the meaning is clear:
the formula is processed by first taking its universal closure, then
negating. The formula is then handled exactly as if it had been input in
`formulas(sos)`, that is, by Skolemizing and transforming to clauses.

### Multiple Goals

If there is more than one formula in `formulas(goals)`, the meaning is
not clear. Is the conclusion the disjunction of those formulas? Or the
conjunction? *The answer: disjunction*: if any goal is proved, the proof
is reported, printed, and counted.

Multiple *complex* goals are not allowed, because the quantification of
free variables can be very confusing. Therefore Prover9 enforces the
following rule.

> *If there is more than one formula in the goals list, each must be a
> positive universal conjunctive formula, that is a formula constructed
> from atomic formulas, universal quantification, and conjunction only.*

To avoid this restriction, one can always write the conclusion clearly
as a single goal formula containing any of the logic connectives and
quantification. However, if the conjecture involves multiple complex
conclusions, we recommend, for search efficiency, separate Prover9
searches.

If there are multiple goals, each is processed separately by applying
universal closure, negation, and transformation to clauses. After this
processing, Prover9 forgets that there were multiple goals and simply
searches for refutations.

When there are multiple goals, and when the user wishes to prove more
than one goal, the parameter [**`max_proofs`**](goals.html#max_proofs)
should be set to an appropriate value. (The flag
[**`auto_denials`**](goals.html#auto_denials) (default set) can do so
automatically.)

## Multiple Proofs

``` my_option
assign(max_proofs, n).  % default n=1, range [-1 .. INT_MAX]
```

> This parameter tells Prover9 to stop searching when the *n*-th proof
> has been found.

## Denials: Negative Clauses in Horn Sets

Denial clauses (negative clauses in Horn sets) can be derived from
goals, or they can be input directly as negative clauses.

### Multiple Proofs of the Same Conclusion

``` my_option
set(reuse_denials).
clear(reuse_denials).    % default clear
```

> If this flag is set, when a denial clause (a negative clause in a Horn
> set) is used in a proof, and when
> [**`max_proofs`**](goals.html#max_proofs) says to search for more
> proofs, subsequent proofs may be of the same conclusion. (Multiple
> proofs of the same conclusion may be useful when one is searching for
> *short* proofs.)
>
> If this flag is clear, then when a proof is found, the denial and all
> of its descendants are disabled so that they will not appear in
> subsequent proofs.
>
> This flag is independent of the flag
> [**`restrict_denials`**](goals.html#restrict_denials).

### Auto_denials

``` my_option
set(auto_denials).    % default set
clear(auto_denials).
```

> If this flag is set (the default), negative clauses in [Horn
> sets](glossary.html#horn) receive some special initial processing.
>
> If a Horn set has more than one denial (negative) clause, we assume
> they correspond to separate conclusions, and the user wishes to have a
> separate proof of each conclusion. Therefore, if
> [**`max_proofs`**](goals.html#max_proofs) has not been changed from
> its default value of 1, we assign to
> [**`max_proofs`**](goals.html#max_proofs) the number of negative
> clauses. (Note that when
> [**`reuse_denials`**](goals.html#reuse_denials) is clear (the
> default), Prover9 prevents multiple proofs of the same conclusion.)
>
> Also, if a negative clause in a Horn set has label attribute but no
> answer attribute, the clause is given an answer attribute
> corresponding to the first label attribute. This saves the user from
> changing "label" to "answer" when moving formulas from the `sos` list
> to the `goals` list.

### Forward or Direct Proofs

The following flag restricts the use of negative clauses, with the aim
of finding proofs that are more direct; that is, proofs that go forward
from the hypotheses to the conclusion rather than proofs that reason
backward from the conclusion.

Ordinarily, the term *denial* refers to a negative clause in a Horn set.
Here, we use it for any negative clause. Originally, the flag
[**`restrict_denials`**](goals.html#restrict_denials) applied only to
Horn sets, but we eliminated that restriction when we realized that it
can be useful for non-Horn sets. However, its use has been well analyzed
for non-Horn sets.

``` my_option
set(restrict_denials).
clear(restrict_denials).    % default clear
```

> If the flag is set, negative clauses (clauses in which all literals
> are negative) are referred to as *restricted denials* and are given
> special treatment.
>
> The inference rules (i.e., paramodulation and the resolution rules)
> will not be applied to restricted denials. However, restricted denials
> will be simplified by [back demodulation](glossary.html#demodulation)
> and [back unit deletion](glossary.html#unit-deletion).
>
> In addition, restricted denials will not be deleted if they are over
> the weight limit ([**`max_weight`**](process-inf.html#max_weight)).
>
> The effect of setting
> [**`restrict_denials`**](goals.html#restrict_denials) is that proofs
> will usually be more forward or direct. This option can speed up
> proofs, it can delay proofs, and it can block all proofs.

## An Example

The following example illustrates multiple goals (including a goal that
is a combination of other goals),
[**`auto_denials`**](goals.html#auto_denials), and
[**`restrict_denials`**](goals.html#restrict_denials).

``` my_job
prover9 -f olsax.in > olsax.out
```

------------------------------------------------------------------------

Next Section: [Production Mode](production.html)


------------------------------------------------------------------------

*Prover9 Manual*


*Version 2009-11A*

------------------------------------------------------------------------

# Prover9 Options

There are three kinds of options:

- *Flags* are Boolean-valued options which can be changed with the *set*
  and *clear* commands, e.g.,
  `set(clocks)`.
  `set(print_given)`.
- *Parms* are integer-valued options which can be changed with the
  *assign* command, e.g.,
  `assign(max_weight, 30)`.
- *Stringparms* are string-valued options which can be changed with the
  *assign* command, e.g.,
  `assign(order, kbo)`.

## Option Dependencies

Several of the flags and parameters cause other flags and parameters to
be changed. In some cases, that is the only direct effect they have. For
example, if you `clear(auto)`, you will see the following in the output.

``` my_file
clear(auto).
    % clear(auto) -> clear(auto_inference).
    % clear(auto_inference) -> clear(predicate_elim).
    % clear(auto_inference) -> assign(eq_defs, pass).
    % clear(auto) -> clear(auto_limits).
    % clear(auto_limits) -> assign(max_weight, 2147483647).
    % clear(auto_limits) -> assign(sos_limit, -1).
```

The lines starting with "`%`" are the dependent options that are changed
in behalf of `clear(auto)`. Note the sub-dependencies in this example.

The option dependencies can be undone by simply changing the dependent
option afterward, as in the following example input.

``` my_file
clear(auto).
set(predicate_elim).
```

## Option Listing

The option names below are links to the sections containing the
descriptions.

### From Page [Clauses and Formulas](syntax.html)

``` my_option
set(prolog_style_variables).
clear(prolog_style_variables).    % default clear
```

### From Page [Automatic Modes](auto.html)

``` my_option
set(auto).    % default set
clear(auto).
```

``` my_option
set(auto_inference).    % default set
clear(auto_inference).
```

``` my_option
set(auto_process).    % default set
clear(auto_process).
```

``` my_option
set(auto_setup).    % default set
clear(auto_setup).
```

``` my_option
set(auto_limits).    % default set
clear(auto_limits).
```

``` my_option
set(auto2).
clear(auto2).    % default clear
```

``` my_option
assign(lrs_ticks, n).  % default n=-1, range [-1 .. INT_MAX]
```

``` my_option
assign(lrs_interval, n).  % default n=50, range [1 .. INT_MAX]
```

``` my_option
assign(min_sos_limit, n).  % default n=0, range [0 .. INT_MAX]
```

``` my_option
set(raw).
clear(raw).    % default clear
```

### From Page [Term Ordering](term-order.html)

``` my_option
assign(order, string).  % default string=lpo, range [lpo,rpo,kbo]
```

``` my_option
set(inverse_order).    % default set
clear(inverse_order).
```

``` my_option
assign(eq_defs, string).  % default string=unfold, range [unfold,fold,pass]
```

### From Page [More Search Prep](more-prep.html)

``` my_option
set(expand_relational_defs).
clear(expand_relational_defs).    % default clear
```

``` my_option
set(predicate_elim).    % default set
clear(predicate_elim).
```

``` my_option
assign(fold_denial_max, n).  % default n=0, range [-1 .. INT_MAX]
```

``` my_option
set(sort_initial_sos).
clear(sort_initial_sos).    % default clear
```

``` my_option
set(process_initial_sos).    % default set
clear(process_initial_sos).
```

### From Page [Search Limits](limits.html)

``` my_option
assign(sos_limit, n).  % default n=20000, range [-1 .. INT_MAX]
```

``` my_option
assign(max_given, n).  % default n=-1, range [-1 .. INT_MAX]
```

``` my_option
assign(max_kept, n).  % default n=-1, range [-1 .. INT_MAX]
```

``` my_option
assign(max_megs, n).  % default n=200, range [-1 .. INT_MAX]
```

``` my_option
assign(max_seconds, n).  % default n=-1, range [-1 .. INT_MAX]
```

``` my_option
assign(max_minutes, n).  % default n=-1, range [-1 .. INT_MAX]
```

``` my_option
assign(max_hours, n).  % default n=-1, range [-1 .. INT_MAX]
```

``` my_option
assign(max_days, n).  % default n=-1, range [-1 .. INT_MAX]
```

### From Page [Selecting the Given Clause](select.html)

``` my_option
assign(age_part, n).     % default n=1, range [0 .. INT_MAX]
```

``` my_option
assign(weight_part, n).  % default n=0, range [0 .. INT_MAX]
```

``` my_option
assign(false_part, n).   % default n=4, range [0 .. INT_MAX]
```

``` my_option
assign(true_part, n).    % default n=4, range [0 .. INT_MAX]
```

``` my_option
assign(random_part, n).  % default n=0, range [0 .. INT_MAX]
```

``` my_option
assign(hints_part, n).   % default n=INT_MAX, range [0 .. INT_MAX]
```

``` my_option
set(default_parts).      % default set
clear(default_parts).
```

``` my_option
assign(pick_given_ratio, n).  % default n=0, range [0 .. INT_MAX]
```

``` my_option
set(lightest_first).
clear(lightest_first).    % default clear
```

``` my_option
set(breadth_first).
clear(breadth_first).    % default clear
```

``` my_option
set(random_given).
clear(random_given).    % default clear
```

``` my_option
assign(random_seed, n).  % default n=0, range [-1 .. INT_MAX]
```

``` my_option
set(input_sos_first).    % default set
clear(input_sos_first).
```

### From Page [Inference Rules](inf-rules.html)

``` my_option
set(binary_resolution).
clear(binary_resolution).    % default clear
```

``` my_option
set(neg_binary_resolution).
clear(neg_binary_resolution).    % default clear
```

``` my_option
set(ordered_res).    % default set
clear(ordered_res).
```

``` my_option
set(check_res_instances).
clear(check_res_instances).    % default clear
```

``` my_option
assign(literal_selection, string).  % default string=max_negative, range [max_negative, all_negative, none]
```

``` my_option
set(pos_hyper_resolution).
clear(pos_hyper_resolution).    % default clear
```

``` my_option
set(hyper_resolution).
clear(hyper_resolution).    % default clear
```

``` my_option
set(neg_hyper_resolution).
clear(neg_hyper_resolution).    % default clear
```

``` my_option
set(ur_resolution).
clear(ur_resolution).    % default clear
```

``` my_option
set(pos_ur_resolution).
clear(pos_ur_resolution).    % default clear
```

``` my_option
set(neg_ur_resolution).
clear(neg_ur_resolution).    % default clear
```

``` my_option
set(initial_nuclei).
clear(initial_nuclei).    % default clear
```

``` my_option
assign(ur_nucleus_limit, n).  % default n=-1, range [-1 .. INT_MAX]
```

``` my_option
set(paramodulation).
clear(paramodulation).    % default clear
```

``` my_option
set(ordered_para).    % default set
clear(ordered_para).
```

``` my_option
set(check_para_instances).
clear(check_para_instances).    % default clear
```

``` my_option
set(para_from_vars).    % default set
clear(para_from_vars).
```

``` my_option
assign(para_lit_limit, n).  % default n=-1, range [-1 .. INT_MAX]
```

``` my_option
set(para_units_only).
clear(para_units_only).    % default clear
```

``` my_option
set(basic_paramodulation).
clear(basic_paramodulation).    % default clear
```

### From Page [Processing Inferred Clauses](process-inf.html)

``` my_option
set(lex_order_vars).
clear(lex_order_vars).    % default clear
```

``` my_option
assign(demod_step_limit, n).  % default n=1000, range [-1 .. INT_MAX]
```

``` my_option
assign(demod_increase_limit, n).  % default n=1000, range [-1 .. INT_MAX]
```

``` my_option
set(back_demod).      % default set
clear(back_demod).
```

``` my_option
set(lex_dep_demod).    % default set
clear(lex_dep_demod).
```

``` my_option
assign(lex_dep_demod_lim, n).  % default n=11, range [-1 .. INT_MAX]
```

``` my_option
set(lex_dep_demod_sane).    % default set
clear(lex_dep_demod_sane).
```

``` my_option
set(unit_deletion).
clear(unit_deletion).    % default clear
```

``` my_option
set(cac_redundancy).    % default set
clear(cac_redundancy).
```

``` my_option
assign(max_literals, n).  % default n=-1, range [-1 .. INT_MAX]
```

``` my_option
assign(max_depth, n).  % default n=-1, range [-1 .. INT_MAX]
```

``` my_option
assign(max_vars, n).  % default n=-1, range [-1 .. INT_MAX]
```

``` my_option
assign(max_weight, n).  % default n=100, range [INT_MIN .. INT_MAX]
```

``` my_option
set(safe_unit_conflict).
clear(safe_unit_conflict).    % default clear
```

``` my_option
set(factor).
clear(factor).    % default clear
```

``` my_option
assign(new_constants, n).  % default n=0, range [-1 .. INT_MAX]
```

``` my_option
set(back_subsume).    % default set
clear(back_subsume).
```

``` my_option
assign(backsub_check, n).  % default n=500, range [-1 .. INT_MAX]
```

### From Page [Output Files](output.html)

``` my_option
set(echo_input).    % default set
clear(echo_input).
```

``` my_option
set(quiet).
clear(quiet).    % default clear
```

``` my_option
set(print_initial_clauses).    % default set
clear(print_initial_clauses).
```

``` my_option
set(print_given).    % default set
clear(print_given).
```

``` my_option
set(print_gen).
clear(print_gen).    % default clear
```

``` my_option
set(print_kept).
clear(print_kept).    % default clear
```

``` my_option
set(print_labeled).
clear(print_labeled).    % default clear
```

``` my_option
set(print_clause_properties).
clear(print_clause_properties).    % default clear
```

``` my_option
set(print_proofs).    % default set
clear(print_proofs).
```

``` my_option
set(default_output).    % default set
clear(default_output).
```

``` my_option
assign(report, n).  % default n=-1, range [-1 .. INT_MAX]
```

``` my_option
assign(stats, string).  % default string=lots, range [none,some,lots,all]
```

``` my_option
set(clocks).
clear(clocks).    % default clear
```

``` my_option
set(bell).    % default set
clear(bell).
```

### From Page [Weighting](weight.html)

``` my_option
assign(constant_weight, n).  % default n=1, range [INT_MIN .. INT_MAX]
```

``` my_option
assign(sk_constant_weight, n).  % default n=1, range [INT_MIN .. INT_MAX]
```

``` my_option
assign(variable_weight, n).  % default n=1, range [INT_MIN .. INT_MAX]
```

``` my_option
assign(not_weight, n).  % default n=0, range [INT_MIN .. INT_MAX]
```

``` my_option
assign(or_weight, n).  % default n=0, range [INT_MIN .. INT_MAX]
```

``` my_option
assign(prop_atom_weight, n).  % default n=1, range [INT_MIN .. INT_MAX]
```

``` my_option
assign(nest_penalty, n).  % default n=0, range [0 .. INT_MAX]
```

``` my_option
assign(depth_penalty, n).  % default n=0, range [INT_MIN .. INT_MAX]
```

``` my_option
assign(var_penalty, n).  % default n=0, range [INT_MIN .. INT_MAX]
```

``` my_option
assign(default_weight, n).  % default n=INT_MAX, range [INT_MIN .. INT_MAX]
```

### From Page [Goals and Denials](goals.html)

``` my_option
assign(max_proofs, n).  % default n=1, range [-1 .. INT_MAX]
```

``` my_option
set(reuse_denials).
clear(reuse_denials).    % default clear
```

``` my_option
set(auto_denials).    % default set
clear(auto_denials).
```

``` my_option
set(restrict_denials).
clear(restrict_denials).    % default clear
```

### From Page [Hints](hints.html)

``` my_option
set(breadth_first_hints).
clear(breadth_first_hints).    % default clear
```

``` my_option
set(degrade_hints).    % default set
clear(degrade_hints).
```

``` my_option
set(limit_hint_matchers).
clear(limit_hint_matchers).    % default clear
```

``` my_option
set(back_demod_hints).    % default set
clear(back_demod_hints).
```

``` my_option
set(collect_hint_labels).
clear(collect_hint_labels).    % default clear
```

### From Page [Semantic Guidance](semantics.html)

``` my_option
assign(multiple_interps, string).  % default string=false_in_all, range [false_in_all, false_in_some]
```

``` my_option
assign(eval_limit, n).  % default n=1024, range [-1 .. INT_MAX]
```

------------------------------------------------------------------------

Next Section: [Glossary](glossary.html)


------------------------------------------------------------------------

*Prover9 Manual*


*Version 2009-11A*

------------------------------------------------------------------------

# Automatic Modes

> Prover9's automatic mode is set by default. Otter's automatic mode
> must be explicitly set.

If you simply give Prover9 a set of clauses and/or formulas, Prover9
will look at the clauses and decide which inference rules and
clause-processing operations to use. If you don't like the automatic
decisions that Prover9 makes, you can clear the flag
[**`auto`**](auto.html#auto) or any of the secondary auto flags that
depend on it. Prover9 output files show in detail the effects of
changing these flags.

``` my_option
set(auto).    % default set
clear(auto).
```

> This is the basic automatic mode of Prover9. The only direct effect of
> this flag is that it changes four secondary auto flags as follows.
>
>       set(auto) -> set(auto_inference).
>       set(auto) -> set(auto_process).
>       set(auto) -> set(auto_setup).
>       set(auto) -> set(auto_limits).
>       set(auto) -> set(auto_denials).
>
>       clear(auto) -> clear(auto_inference).
>       clear(auto) -> clear(auto_process).
>       clear(auto) -> clear(auto_setup).
>       clear(auto) -> clear(auto_limits).
>       clear(auto) -> clear(auto_denials).
>
> Any of the secondary flags, as well as the entire automatic mode can
> be cleared by the user.

``` my_option
set(auto_inference).    % default set
clear(auto_inference).
```

> If this flag is set, the input clauses are checked for several
> syntactic properties such as the presence of equality and
> [non-Horn](glossary.html#horn) clauses. Based on the results of the
> checks, Prover9 decides which inference rules to use.
>
> Unlike ordinary option dependencies, the options that are changed by
> [**`auto_inference`**](auto.html#auto_inference) cannot be undone by
> placing commands in the input file, because they depend on the
> structure of the clauses.

``` my_option
set(auto_process).    % default set
clear(auto_process).
```

> This flag causes several other flags that affect clause processing to
> be altered based syntactic properties of the initial clauses.
>
> If all clauses are Horn and there are negative nonunits, the flag
> [**`back_unit_deletion`**](process-inf.html#back_unit_deletion) is
> automatically set. If there are non-Horn clauses, the flags
> [**`back_unit_deletion`**](process-inf.html#back_unit_deletion) and
> [**`factor`**](process-inf.html#factor) are automatically set.
>
> Unlike ordinary option dependencies, the options that are changed by
> [**`auto_process`**](auto.html#auto_process) cannot be undone by
> placing commands in the input file, because they depend on the
> structure of the clauses.

``` my_option
set(auto_setup).    % default set
clear(auto_setup).
```

> The only effect of changing this flag is that two parameters are
> changed in the following ways.
>
>       set(auto_setup) -> set(predicate_elim).
>       set(auto_setup) -> assign(eq_defs, unfold).
>
>       clear(auto_setup) -> clear(predicate_elim).
>       clear(auto_setup) -> assign(eq_defs, pass).

``` my_option
set(auto_limits).    % default set
clear(auto_limits).
```

> The only effect of changing this flag is that two parameters are
> changed in the following ways.
>
>       set(auto_limits) -> assign(max_weight, 100).
>       set(auto_limits) -> assign(sos_limit, 10000).
>
>       clear(auto_limits) -> assign(max_weight, INT_MAX).
>       clear(auto_limits) -> assign(sos_limit, -1).

## An Experimental Automatic Mode

``` my_option
set(auto2).
clear(auto2).    % default clear
```

> This is an enhanced automatic mode, developed in preparation for
> CASC-2005. The only direct effect of changing this option is that it
> causes several other options to be changed. See an output file to see
> the effects of setting this flag.

## Automatically Adjusting the [**`sos_limit`**](limits.html#sos_limit) Parameter

``` my_option
assign(lrs_ticks, n).  % default n=-1, range [-1 .. INT_MAX]
```

``` my_option
assign(lrs_interval, n).  % default n=50, range [1 .. INT_MAX]
```

``` my_option
assign(min_sos_limit, n).  % default n=0, range [0 .. INT_MAX]
```

> These three parameters work together and are used to automatically
> adjust the parameter [**`sos_limit`**](limits.html#sos_limit) by means
> of a "limited resource strategy" \[[RV-lrs](references.html#RV-lrs)\].
> If [**`lrs_ticks`**](auto.html#lrs_ticks) ≥ 0, the method is applied.
>
> This is an experimental feature and is not recommended for general
> use.

## Raw Mode

The default values of the options can interfere with specialized search
strategies. To avoid some of those problems, one can start from scratch
by setting the following option.

``` my_option
set(raw).
clear(raw).    % default clear
```

> This is a sort of anti-automatic mode, which allows the user to
> completely specify the search strategy, with less chance of
> interference from the default settings of various options. For
> example, to generate all binary resolvents, one can simply set the
> flags `raw` and
> [**`binary_resolution`**](inf-rules.html#binary_resolution) instead of
> finding and clearing the flags that restrict resolution.
>
> The flag works by making the following changes.
>
>        set(raw) -> clear(auto).
>        clear(auto) -> clear(auto_inference).
>        clear(auto) -> clear(auto_setup).
>        clear(auto_setup) -> clear(predicate_elim).
>        clear(auto_setup) -> assign(eq_defs, pass).
>        clear(auto) -> clear(auto_limits).
>        clear(auto_limits) -> assign(max_weight, 2147483647).
>        clear(auto_limits) -> assign(sos_limit, -1).
>        clear(auto) -> clear(auto_denials).
>        clear(auto) -> clear(auto_process).
>        set(raw) -> clear(ordered_res).
>        set(raw) -> clear(ordered_para).
>        set(raw) -> assign(literal_selection, none).
>        set(raw) -> clear(back_demod).
>        set(raw) -> clear(cac_redundancy).
>        set(raw) -> assign(backsub_check, 2147483647).
>        set(raw) -> set(lightest_first).
>        set(lightest_first) -> assign(weight_part, 1).
>        set(lightest_first) -> assign(age_part, 0).
>        set(lightest_first) -> assign(false_part, 0).
>        set(lightest_first) -> assign(true_part, 0).
>        set(lightest_first) -> assign(random_part, 0).

------------------------------------------------------------------------

Next Section: [Term Ordering](term-order.html)


------------------------------------------------------------------------

*Prover9 Manual*


*Version 2009-11A*

------------------------------------------------------------------------

# Output Files

Even when Prover9 fails to find a proof, its output file usually has
lots of valuable information about the search. The output file can
suggest many ways of improving the search for subsequent jobs as in the
following examples.

- The output shows how equalities are oriented; different [term ordering
  parameters](term-order.html) may give better or more intuitive
  orientations.
- If Prover9 focused the search on uninteresting clauses (see the
  sequence of given clauses), different [inference
  rules](inf-rules.html), a different
  [**`pick_given_ratio`**](select.html#pick_given_ratio), or a
  specialized [weighting function](weight.html) can be used.
- If Prover9 ran out of time or memory with a huge `sos` list and small
  `usable` list (i.e., few given clauses were used), the
  [**`sos_limit`**](limits.html#sos_limit) should be reduced.

## Basic Structure of Output Files

Prover9 output files are divided into sections and subsections so the
users (people and programs) can find what they are looking for. The
delimiters are self-explanatory. A few comments about the sections are
given here. For a specific example, see the output file
[subset_trans.out](subset_trans.out).

``` my_file
============================== Prover9 ===============================
    Version, date, host computer, command.
============================== end of head ===========================

============================== INPUT =================================
    Echo of the input.  Everything in this section that is not
    in the input is commented with "%", so copy-and-paste can be
    done on this section to create a new input file.
============================== end of input ==========================

============================== PROCESS GOALS =========================
    The search is always by refutation, and this section shows
    how goals are negated in preparation for the search.
============================== end of process goals ==================

============================== PROCESS INITIAL CLAUSES ===============
    This section shows the starting clauses (after Skomemization,
    if applicable) and then some of what Prover9 does in preparation
    for the search.  This includes predicate_elim, term ordering
    decisions, and auto_inference settings.  At this stage, clauses
    may be deleted by subsumption and equations may be copied to the
    list demodulators.  See the flag process_initial_sos.
============================== end of process initial clauses ========

============================== CLAUSES FOR SEARCH ====================
    This section shows the clauses just before the start of the
    search, that is, just before selection of the first given clause.

============================== end of clauses for search =============

============================== SEARCH ================================
    This section typically shows the sequence of given clauses,
    and it may also include PROOF and STATISTICS sections.

============================== PROOF =================================
    A proof in standard form.
============================== end of proof ==========================

============================== STATISTICS ============================
    We encourage users to look at statistics!
============================== end of statistics =====================

============================== end of search =========================
```

## Clause Justifications

After the initial stage of the output, each clause in the file has an
integer identifier (ID) and a justification that may refer to IDs of
other clauses. A justification is a list consisting of one primary step
and some number of secondary steps. Most primary steps are inference
rules applied to given clauses, and most secondary steps consist of
simplification, rewriting, or orienting equalities.

Many of the types of step refer to positions of literals or terms in the
parent clauses. Literals are identified by the characters 'a' (first
literal), 'b' (second literal), etc. Terms are identified by the literal
identifier followed by a sequence of integers giving the position of the
term within the literal. For example, the position 'c,1,3,2' means third
literal, first argument, third argument, second argument. Negation signs
on literals are not included in the sequence.

Primary Steps.

- `assumption` -- input formula.
- `clausify` -- from CNF translation of a non-clausal assumption.
- `goal` -- input formula.
- `deny` -- from CNF translation of the negation of a goal.
- `resolve(59,b,47,c)` -- resolve the second literal of clause 59 with
  the third literal of clause 47.
- `hyper(59, b,47,a, c,38,a)` -- hyperresolution; interpret the list as
  a clause ID followed by a sequence of triples,
  \<literal,clause-ID,literal\> the inference is presented as a sequence
  of binary resolution steps. In the example shown, start with clause
  59; then resolve literal b with clause 47 on literal a; with the
  result of the first step, resolve literal c with clause 38 on
  literal a. The special case "`xx`" means resolution with `x=x`.
- `ur(39, a,48,a, b,88,a, c,87,a, d,86,a)` -- unit-resulting resolution;
  the list is interpreted as in hyperresolution.
- `para(47(a,1),28(a,1,2,2,1))` -- paramodulate from the clause 47 into
  clause 28 at the positions shown.
- `copy(59)` -- copy clause 59.
- `back_rewite(59)` -- copy clause 59.
- `back_unit_del(59)` -- copy clause 59.
- `new_symbol(59)` -- introduce a new constant (see parameter
  [**`new_constants`**](inf-rules.html#new_constants)).
- `factor(59,b,c)` -- factor clause 59 by unifying the second and third
  literals.
- `xx_res(59,b)` -- resolve the second literal of clause 59 with `x=x`.
- `propositional` -- not used in standard proofs.
- `instantiate` -- not used in standard proofs.
- `ivy` -- not used in standard proofs.

Secondary Steps (each assumes a working clause, which is either the
result of a primary step or a previous secondary step).

- `rewrite([38(5,R),47(5),59(6,R)])` -- rewriting (demodulation) with
  equations 38, 47, then 59; the arguments (5), (5), and (6) identify
  the positions of the rewritten subterms (in an obscure way), and the
  argument R indicates that the demodulator is used backward
  (right-to-left).
- `flip(c)` -- the third literal is an equality that has been flipped by
  the term ordering. This does not necessarily mean that the equality is
  orientable by the primary term ordering, e.g., KBO.
- `merge(d)` -- the fourth literal has been removed because it was
  identical to a preceding literal.
- `unit_del(b,38)` -- the second literal has been removed because it was
  an instance of the negation clause 38 (which is a unit clause).
- `xx(b)` -- the second literal has been removed because it was an
  instance of `x!=x`.

## Standard Proofs

Prover9 proofs may be transformed by separate programs, e.g., by
[Prooftrans](prooftrans.html).

## Options That Say What Goes To the Output File

``` my_option
set(echo_input).    % default set
clear(echo_input).
```

> Clearing this flag suppresses printing of clauses, formulas, weighting
> rules (and everything else that ends with `end_of_list`) that would
> ordinarily appear in the `INPUT` section of the output file.

``` my_option
set(quiet).
clear(quiet).    % default clear
```

> Setting this flag causes most messages to the standard error file
> (usually the user's screen) to be suppressed. These messages include
> notifications about proofs and statistics reports, and warnings about
> demodulation limits. Setting this flag also suppresses several
> messages to the ordinary output file, and it clears the
> [**`bell`**](output.html#bell) flag.

``` my_option
set(print_initial_clauses).    % default set
clear(print_initial_clauses).
```

> If this flag is set, clauses are printed in the
> `PROCESS INITIAL CLAUSES` and `CLAUSES FOR SEARCH` sections of the
> output file.

``` my_option
set(print_given).    % default set
clear(print_given).
```

> Clearing this flag prevents given clauses from being printed to the
> output file.

``` my_option
set(print_gen).
clear(print_gen).    % default clear
```

> Setting this flag causes all generated clauses to be printed to the
> the output file. In addition, some other information about the
> processing of each generated clause is printed. This flag can be
> output files to be really huge.

``` my_option
set(print_kept).
clear(print_kept).    % default clear
```

> Setting this flag causes all kept clauses to be printed to the the
> output file. In addition, some other information on the processing of
> kept clauses is printed.

``` my_option
set(print_labeled).
clear(print_labeled).    % default clear
```

> Setting this flag causes kept clauses containing label attributes to
> be printed, even when the flag
> [**`print_kept`**](output.html#print_kept) is clear. This flag is
> useful when using [the hints strategy](hints.html), because when a
> clause matches a hint containing a label, the label is copied to the
> clause. That is, clauses matching labeled hints will be printed.

``` my_option
set(print_clause_properties).
clear(print_clause_properties).    % default clear
```

> Setting this flag causes several properties of clauses to be printed
> as "props" attributes on the clauses. The properties include which
> literals are maximal (counting from 1), which literals are maximal
> among literals of the same sign, and which literals are selected for
> application of inference rules.

``` my_option
set(print_proofs).    % default set
clear(print_proofs).
```

> Clearing this flag prevents proofs from being printed to the output
> file. The proof message still goes to the standard error file (usually
> the user's screen), unless the flag [**`quiet`**](output.html#quiet)
> has been set.

``` my_option
set(default_output).    % default set
clear(default_output).
```

> Setting this flag restores most of the output flags and parameters to
> their default values. Clearing this flag does nothing.

``` my_option
assign(report, n).  % default n=-1, range [-1 .. INT_MAX]
```

> If *n* \> 0, statistics are sent to the output file approximately
> every *n* seconds. (On Unix-like systems, one can also tell Prover9 to
> print statistics to the output file by sending the signal `USR1` to a
> running Prover9 process, e.g., `kill -USR1 4223`.)

``` my_option
assign(stats, string).  % default string=lots, range [none,some,lots,all]
```

> This parameter determines how many statistics are sent to the output
> file.

``` my_option
set(clocks).
clear(clocks).    % default clear
```

> If this flag is set, various operations during the Prover9 job are
> timed (e.g., inference, demodulation, and subsumption), and timing
> reports are sent to the output file.
>
> Timing the operations can be expensive, especially in Solaris and
> Macintosh systems. On Linux systems, `set(clocks)` typically adds 5%
> -- 10% to the run time.

``` my_option
set(bell).    % default set
clear(bell).
```

> If this flag is set, Prover9 beeps when important things happen, such
> as proofs and warnings. Some users run searches that find hundreds of
> proofs, and they clear this flag to prevent all of the beeping.

------------------------------------------------------------------------

Next Section: [Weighting](weight.html)


------------------------------------------------------------------------

*Prover9 Manual*


*Version 2009-11A*

------------------------------------------------------------------------

# Mace4 (Models And CounterExamples)

The program [Mace4](http://www.cs.unm.edu/~mccune/mace4/)
\[[McCune-Mace4](references.html#McCune-Mace4)\] searches for finite
structures satisfying first-order and equational statements (the same
kind of statement that Prover9 accepts). If the statement is the denial
of some conjecture, any structures found by Mace4 are counterexamples to
the conjecture.

Mace4 can be a valuable complement to Prover9, looking for
counterexamples before (or at the same time as) using Prover9 to search
for a proof. It can also be used to help debug input clauses and
formulas for Prover9.

For the most part, Mace4 accepts the same input files as Prover9. If the
input file contains commands that Mace4 does not understand, then the
argument "-c" must be given to tell Mace4 to ignore those commands.

For example, say we're learning group theory, and we're wondering
whether all groups are commutative. We can run the following two jobs in
parallel, with Prover9 looking for a proof, and Mace4 looking for a
counterexample.

``` my_job
prover9  -f x2.in > x2.prover9.out
mace4 -c -f x2.in > x2.mace4.out
```

Most of the options accepted by Mace4 can be given either on the command
line or in the input file. The following command lists the command-line
options accepted by Mace4.

``` my_job
mace4 -help
```

**Terminology**. We use the terms *interpretation*, *model*, and
*structure* for the objects that Mace4 produces. From a logic point of
view, Mace4 produces interpretations which are models of the input
formulas. From a math point of view, Mace4 produces structures
satisfying the input formulas.

## What Mace4 Does

Mace4 searches for *unsorted finite structures* only. That is, a
structure (model) has one underlying finite set, called the *domain*
(the members are always 0,1,...,*n-1* for a set of size *n*), and
structures are functions and relations (tables) over the domain,
corresponding to the operations and relation symbols in the
specification.

By default, Mace4 starts searching for a structure of domain size 2, and
then it increments the size until it succeeds or reaches some limit.

## The Original Mace4 Manual

The original Mace4 manual
\[[McCune-Mace4](references.html#McCune-Mace4)\]
([PDF)](http://www.cs.unm.edu/~mccune/prover9/mace4.pdf) is out of date
with respect to features and options, but it contains useful information
on the history of Mace4, details on the search methods, and the
differences between Mace2 and Mace4.

------------------------------------------------------------------------

Next Section: [Mace4 Input](m4-input.html)


------------------------------------------------------------------------

*Prover9 Manual*


*Version 2009-11A*

------------------------------------------------------------------------

# Mace4 Input

Mace4 has been designed so that it accepts most Prover9 input files.
This allows users to prepare one input file which can be used by Prover9
(to search for proofs) and by Mace4 (to search for counterexamples).

## Mace4 Options

Mace4 and Prover9 accept different sets of flags and parameters. In
order to use the same input files for both programs, we let Mace4 take
its options from the command line instead of from the input file. If
Mace4 is given a Prover9 input file, along with the command-line option
`-c`, it will ignore any unrecognized (e.g., Prover9) options in the
input file. The Mace4 options are described on the [next
page](m4-options.html).

## Formulas (including Clauses)

Mace4 accepts the same formulas and clauses as Prover9. See the page
[Prover9 Clauses and Formulas](syntax.html).

### *A Caveat: Domain Elements*

> In one important case, formulas have different meanings in Prover9 and
> Mace4:

If a formula contains constants that are natural-numbers, {0,1,...},
Mace4 assumes they are members of the domain of some structure, that is,
they are distinct objects; in effect, Mace4 operates under the
assumptions 0 ≠ 1, 0 ≠ 2, ... .

To Prover9, natural numbers are just ordinary constants. For example, to
Prover9 the statement 0=1 is satisfiable, and to Mace4 it is
unsatisfiable.

Because Mace4 assumes that natural-number constants are members of the
domain, if a formula contains a natural number that is out of range (≥
*n*), when searching for a structure of size *n*), Mace4 will terminate
its search for size *n* (and continue with larger sizes if the
specification says to do so).

*An Exception.* When the flag `arithmetic` is set, natural numbers
outside of {0,1,...,n-1} can occur.

## Lists of Formulas (including Clauses)

Prover9 accepts a fixed set of lists of formulas (e.g., `assumptions`,
`usable`, `goals`, `hints`).

Mace4 accepts any lists of formulas. All are treated as ordinary
formulas *except the following two lists*.

- `formulas(hints)`. These are intended to help Prover9 find proofs and
  are ignored by Mace4.
- `formulas(goals)`. These are negated by Mace4, just as they are by
  Prover9.

### `formulas(goals)`

Prover9 has several restrictions on the goals it accepts (see [Prover9
Goals and Denials](goals.html)), and Mace4 has the same restrictions.
Mace4 negates goals and translates them to clauses in the same way as
Prover9. (The term "goal" might seem to be bad teminology for Mace4
users, because Mace4 does not prove theorems; however, one can think of
Mace4 as searching for a counterexample to the goal.)

When there are multiple goals, Mace handles them the same as Prover9.
For example, consider the following goals.

``` my_file
formulas(goals).
  x * y = y * x              # label(commutativity).
  (x * y) * z = x * (y * z)  # label(associativity).
end_of_list.
```

Logically, this is a disjunction: Prover9 gives a proof if either goal
is proved, and Mace4 gives a counterexample if both are falsified. In
particular, this pair of goals is equivalent (for both Prover9 and
Mace4) to the following pair of assumptions.

``` my_file
formulas(assumptions).
  exists x exists y (x * y != y * x).
  exists x exists y exists z (x * y) * z != x * (y * z).
end_of_list.
```

## Distinct Objects

Mace4 accepts a shorthand method for stating that sets of objects are
distinct. Here is an example of two sets of distinct objects.

``` my_file
list(distinct).
[a,b,c].     % equivalent to (a!=b & a!=c & b!=c).
[d,e,f(a)].  % equivalent to (d!=e & d!=f(a) & e!=f(a)).
end_of_list.
```

Although `list(distinct)` will probably be used mostly for constants and
other ground terms, terms with variables can occur.

------------------------------------------------------------------------

Next Section: [Mace4 Options](m4-options.html)


------------------------------------------------------------------------

*Prover9 Manual*


*Version 2009-11A*

------------------------------------------------------------------------

# Mace4 Options

Mace4 accepts `set`, `clear`, and `assign` commands in the input file.
Several of these are in common with Prover9 (e.g.,
`assign(max_seconds, 30)`), but most are specifically for Mace4.

If Mace4 is called with the command-line option `-c` (compatability
mode), it will ignore any `set`, `clear`, and `assign` that it does not
recognize, assuming they are meant for some other program (Prover9).

Most Mace4 options can be specified on the command line instead of in
the input file. When Mace4 options are specified on the command line,
single-character codes are used. For example, the command-line option
`-t 30` means the same as `assign(max_second, 30)` in the input file. If
an option is given in *both* places, the one on the command line takes
precedence. Command-line options for Boolean-valued options (flags)
always take an argument: 1 means "set", and 0 means "clear". For
example, `-V 1` means `set(prolog_style_vaiables`, and `-V 0` means
`clear(prolog_style_variables)`.

The command "`mace4 -help`" shows the correspondence between the
command-line codes and the option names, and it shows the default
values.

## Symbol Ordering

Like Prover9, Mace4 accepts `function_order` and `relation_order`
commands that specify an order on the symbols in the problem. The syntax
of the commands is the [same as in
Prover9](term-order.html#lex_command), for example,

``` my_file
predicate_order([=, <=, P, Q]).          % = < P < Q
function_order([a, b, c, +, *, h, g]).   % a < b < c < + < * < h < g
```

Mace4's the default symbol order is the [same as
Prover9's](term-order.html#default_lex). As in Prover9, function symbols
are always less than predicate symbols.

The symbol order can have a big effect on the time it takes to find a
model or exhaust a domain size, because it determines the order in which
Mace4 tries to fill in the function and relation tables. Unfortunately,
we do not know of any general-purpose heuristics for selecting a good
symbol order. If Mace4 takes too long to go through a particular domain
size, we suggest trying a different symbol order.

## Option Listing

### Basic Options

``` my_file
assign(start_size, n).  % default n=2, range [2 .. INT_MAX]  % command-line -n n
```

``` my_file
assign(end_size, n).  % default n=-1, range [-1 .. INT_MAX]  % command-line -N n
```

``` my_file
assign(increment, n).  % default n=1, range [1 .. INT_MAX]  % command-line -i n
```

These three parameter work together to determine the domain sizes to be
searched. The search starts for structures of size `start_size`; if that
search fails, the size is incremented, and another search starts. This
continues up through the value `end_size` (or until some other limit
terminates the process). If `end_size` is -1, there is no limit. (Also
see the `iterate` parameter below.)

For example, the command-line options "`-n 5 -N 11 -i 2`" say to try
domain sizes 5,7,9,11.

``` my_file
assign(domain_size, n).  % default n=0, range [0 .. INT_MAX]  % command-line -n n
```

This parameter says to search *only* the given size. This (meta-)
parameter works simply by making the following changes.

      assign(domain_size, n) -> assign(start_size, n).
      assign(domain_size, n) -> assign(end_size, n).

``` my_file
assign(iterate, string).  % default string=all, range [all,evens,odds,primes,nonprimes]
```

The `iterate` parameter can be used to add an additional constraint to
the domain sizes. It can be used together with the `increment`
parameter. The `iterate` parameter cannot be specified on the command
line.

``` my_file
assign(max_models, n).  % default n=1, range [-1 .. INT_MAX]  % command-line -m n
```

The parameter `max_models` says to stop searching when the *n*-th
structure has been found. A value of -1 means there is no limit.

``` my_file
assign(max_seconds, n).  % default n=-1, range [-1 .. INT_MAX]  % command-line -t n
```

The parameter [**`max_seconds`**](limits.html#max_seconds) says to stop
searching after *n* seconds. A value of -1 means there is no limit.

``` my_file
assign(max_seconds_per, n).  % default n=-1, range [-1 .. INT_MAX]  % command-line -s n
```

The parameter allows at most *n* seconds for each domain size. The
parameter [**`max_seconds`**](limits.html#max_seconds) can be used
(together with `max_seconds_per`) to given an overall time limit. A
value of -1 means there is no limit.

``` my_file
assign(max_megs, n).  % default n=200, range [-1 .. INT_MAX]  % command-line -b n
```

The parameter [**`max_megs`**](limits.html#max_megs) says to stop
searching when (about) *n* megabytes of memory have been used. A value
of -1 means there is no limit.

``` my_file
set(prolog_style_variables).                       % command-line -V 1
clear(prolog_style_variables).    % default clear  % command-line -V 0
```

A rule is needed for distinguishing variables from constants in clauses
and formulas with free variables. If this flag is clear, variables start
with (lower case) 'u' through 'z'. If this flag is set, variables in
clauses start with (upper case) 'A' through 'Z' or '\_'.

``` my_file
set(print_models).      % default set    % command-line -P 1
clear(print_models).                     % command-line -P 0
```

If this flag is set, all structures that are found are printed in
"standard" form, which means they are suitable as input to other LADR
programs such as [isofilter](m4-isofilter.html) and
[interpformat](m4-interpforma.html).

``` my_file
set(print_models_tabular).                       % command-line -p 1
clear(print_models_tabular).    % default clear  % command-line -p 0
```

If this flag is set, and if is clear, all structures that are found are
printed in a tabular form. If both `print_models` and
`print_models_standard` are set, the last one in the input takes effect.

``` my_file
set(integer_ring).                       % command-line -R 1
clear(integer_ring).    % default clear  % command-line -R 0
```

If this flag is set, a ring structure is is applied to the search. The
operations {+,-,\*} are assumed to be the ring of integers (mod
domain_size). This method puts a tight constraint on the search,
allowing much larger structures to be investigated. Here is an example.

``` my_job
mace4 -f ring41.in > ring41.out
```

For further information on the `integer_ring` flag, see [slides from a
workshop
presentation](http://www.cs.unm.edu/~mccune/slides/award-2004.pdf).

``` my_file
set(order_domain).
clear(order_domain).        % default clear
```

If this flag is set, the relations `<` and `<=` are fixed as order
relations on the domain in the obvious way.

``` my_file
set(arithmetic).
clear(arithmetic).        % default clear
```

If this flag is set, several function and relation symbols understood by
Mace4 as operations and relations on the integers, and evaluation of
terms involving those symbols occurs during the search for models. See
the page [Arithmetic for Mace4](m4-arithmetic.html).

``` my_file
set(verbose).                       % command-line -v 1
clear(verbose).    % default clear  % command-line -v 0
```

If the `verbose` flag is set, the output file receives information about
the search, including the initial partial model (the part of the model
that can be determined before backtracking starts) and timing and other
statistics for each domain size. (It does not give a trace of the
backtracking, so it does not consume a lot of file space.)

``` my_file
set(trace).                       % command-line -T 1
clear(trace).    % default clear  % command-line -T 0
```

If the `trace` flag is set, detailed information about the search,
including a trace of all assignments and backtracking, is printed to the
standard output. *This flag causes a lot of output, so it should be used
only on small searches*.

### Advanced Options

These options are used for experimentation with search methods. They can
be ignored by nearly all users. For descriptions of most of these
options, see the original Mace4 manual
\[[McCune-Mace4](references.html#McCune-Mace4)\]
([PDF)](http://www.cs.unm.edu/~mccune/prover9/mace4.pdf).

``` my_file
set(lnh).      % default set    % command-line -L 1
clear(lnh).                     % command-line -L 0
```

``` my_file
assign(selection_order, n).  % default n=2, range [0 .. 2]  % command-line -O n
```

``` my_file
assign(selection_measure, n).  % default n=4, range [0 .. 4]  % command-line -M n
```

``` my_file
set(negprop).      % default set    % command-line -G 1
clear(negprop).                     % command-line -G 0
```

``` my_file
set(neg_assign).      % default set    % command-line -H 1
clear(neg_assign).                     % command-line -H 0
```

``` my_file
set(neg_assign_near).      % default set    % command-line -I 1
clear(neg_assign_near).                     % command-line -I 0
```

``` my_file
set(neg_elim).      % default set    % command-line -J 1
clear(neg_elim).                     % command-line -J 0
```

``` my_file
set(neg_elim_near).      % default set    % command-line -K 1
clear(neg_elim_near).                     % command-line -K 0
```

``` my_file
set(skolems_last).                       % command-line -S 1
clear(skolems_last).    % default clear  % command-line -S 0
```

------------------------------------------------------------------------

Next Section: [Interpformat](m4-arithmetic.html)


------------------------------------------------------------------------

*Prover9 Manual*


*Version 2009-11A*

------------------------------------------------------------------------

# Interpformat

The models (structures) in Mace4 output files can be transformed in
various ways with the program Interpformat.

The transformations are listed here.

- `standard`: This transformation simply extracts the structure from the
  file and reprints it in the same (standard) format, with one line for
  each operation. The result should be acceptable to any of the LADR
  programs that take standard structures.
- `standard2`: This is similar to `standard`, except that the binary
  operations are split across multiple lines to make them more
  human-readable. The result should be acceptable to any of the LADR
  programs that take standard structures.
- `portable`: This form is list of ... of lists of strings and natural
  numbers. It can be parsed by seveal scripting systems such as GAP,
  Python, and Javascript. See the section [Portable Format](#portable).
- `tabular`: This form is designed to be easily readable by humans. It
  is not meant for input to other programs.
- `raw`: This form is a sequence of natural numbers.
- `cooked`: This form is a sequence of ground terms.
- `xml`: This is an XML form. Here is a [DTD](interp3.dtd) for LADR
  interpretations, and here is an [XML stylesheet](interp3.xsl) for
  transforming the XML to HTML.
- `tex`: This generates LaTeX source for the interpretation.

## Examples

The following Mace4 job creates an output file containing one model in
"standard" (the default) format.

``` my_job
mace4 -c -f x2.in > x2.mace4.out
```

The following Interpformat jobs take the Mace4 output file, extract the
model, and transform it as described above.

``` my_job
interpformat standard  -f x2.mace4.out > x2.standard
interpformat standard2 -f x2.mace4.out > x2.standard2
interpformat portable  -f x2.mace4.out > x2.portable
interpformat tabular   -f x2.mace4.out > x2.tabular
interpformat raw       -f x2.mace4.out > x2.raw
interpformat cooked    -f x2.mace4.out > x2.cooked
interpformat xml       -f x2.mace4.out > x2.xml
interpformat tex       -f x2.mace4.out > x2.tex
```

Portable Format

The portable format for interpretations can be parsed by several
scriping languages including [Python](http://www.python.org) and
[GAP](http://www.gap-system.org). Here is a counterexample on ternary
relations in lattice theory. The result contains one interpretation of
size 4 containing two binary functions (meet and join), one binary
relation (less-or-equal), two ternary relations, and three constants.

``` my_job
mace4 -c -f LT-port.in | interpformat portable > LT-port.out
```

The result is a list of interpretations:

- each interpretation is a triple: \[size-of-interpretation (say n),
  comments, list-of-operations\];
- each operation is a 4-tuple: \["function" \| "relation",
  name-of-operation, arity, values\];
- values of operations (domain elememts are \[0 ... n-1\]):
  - constant (nullary function): domain element;
  - unary function: list of domain elements;
  - binary funcion: 2-dimensional list (list of lists) of domain
    elements;
  - ternary funcion: 3-dimensional list of domain elements;
  - etc.
  - relations are similar but with values of 0 (FALSE) or 1 (TRUE).

Here is a simple Python script that reads a list of portable
interpretations and prints them in a different form.

``` my_job
port.py < LT-port.out > LT-port.out2
```

Here is a simple GAP session that reads and prints a list of portable
interpretations.

``` my_screen
% gap -b
GAP4, Version: 4.4.7 of 17-Mar-2006, i486-pc-linux-gnu-i486-linux-gnu-gcc
gap> interpretations := EvalString(StringFile("LT-port.out"));;
gap> interpretations;
[ [ 4, [ "=(number,1)", "=(seconds,0)" ],
      [ [ "relation", "<=", 2, [ [ 1, 1, 1, 1 ], [ 0, 1, 0, 0 ],
                  [ 0, 1, 1, 0 ], [ 0, 1, 0, 1 ] ] ],
          [ "function", "^", 2, [ [ 0, 0, 0, 0 ], [ 0, 1, 2, 3 ],
                  [ 0, 2, 2, 0 ], [ 0, 3, 0, 3 ] ] ],
          [ "function", "v", 2, [ [ 0, 1, 2, 3 ], [ 1, 1, 1, 1 ],
                  [ 2, 1, 2, 1 ], [ 3, 1, 1, 3 ] ] ],
          [ "function", "c1", 0, 2 ], [ "function", "c2", 0, 0 ],
          [ "function", "c3", 0, 3 ],
          [ "relation", "A", 3, [ [ [ 1, 1, 1, 1 ], [ 0, 1, 0, 0 ],
                      [ 0, 1, 1, 0 ], [ 0, 1, 0, 1 ] ],
                  [ [ 1, 0, 0, 0 ], [ 1, 1, 1, 1 ], [ 1, 0, 1, 0 ],
                      [ 1, 0, 0, 1 ] ],
                  [ [ 1, 0, 0, 0 ], [ 0, 1, 0, 0 ], [ 1, 1, 1, 0 ],
                      [ 0, 0, 0, 0 ] ],
                  [ [ 1, 0, 0, 0 ], [ 0, 1, 0, 0 ], [ 0, 0, 0, 0 ],
                      [ 1, 1, 0, 1 ] ] ] ],
          [ "relation", "B", 3, [ [ [ 1, 1, 1, 1 ], [ 0, 1, 0, 0 ],
                      [ 0, 1, 1, 0 ], [ 0, 1, 0, 1 ] ],
                  [ [ 1, 0, 0, 0 ], [ 1, 1, 1, 1 ], [ 1, 0, 1, 0 ],
                      [ 1, 0, 0, 1 ] ],
                  [ [ 1, 0, 0, 1 ], [ 0, 1, 0, 1 ], [ 1, 1, 1, 1 ],
                      [ 0, 0, 0, 1 ] ],
                  [ [ 1, 0, 1, 0 ], [ 0, 1, 1, 0 ], [ 0, 0, 1, 0 ],
                      [ 1, 1, 1, 1 ] ] ] ] ] ] ]
gap>
```

------------------------------------------------------------------------

Next Section: [Isofilter](m4-isofilter.html)


------------------------------------------------------------------------

*Prover9 Manual*


*Version 2009-11A*

------------------------------------------------------------------------

# Prooftrans

When Prover9 proves a theorem, it sends the proof to its output file in
a standard form. The standard form contains, for each step,
[justifications](output.html#just) with enough detail to reconstruct or
check the proof without any search.

Prover9 proofs may contain non-clausal assumptions and
[goals](goals.html), as well as ordinary clauses. Non-clausal
assumptions are translated to clauses, and goals are negated and then
translated to clauses. See the proof in following example

``` my_job
prover9 -f subset_trans.in > subset_trans.out
```

Prooftrans can extract proofs from Prover9 output files and transform
them in various ways, including the following.

- No transformation,
- renumber steps,
- simplify justifications,
- expand all steps, turning secondary justifications into explicit
  steps,
- produce proofs in XML,
- produce proofs for checking by the IVY proof checker, and
- produce hints for guiding subsequent searches.

Prooftrans is part of the LADR/Prover9/Mace4 package. When the package
is installed, the Prooftrans program should be in the same directory as
Prover9 and Mace4.

## Using Prooftrans

The Prover9 output file containing the proof(s) is usually given to
Prooftrans with the argument "`-f <filename>`". If there is no
"`-f <filename>`" argument, Prooftrans takes its input from the standard
input.

The arguments that tell Prooftrans what to do with the proof(s) are
described in the following sections, using the output file
[subset_trans.out](subset_trans.out) as a running example.

If there is more than one proof in the file, the transformations will be
applied to each proof. The `hints` transformation collects all of the
clauses in the proof(s) into one list of hints. The other
transformations produce one proof for each proof in the input file.

Here is a synopsis of the Prooftrans command; the arguments in square
brackets are optional.

``` my_job
prooftrans [parents_only] [expand] [renumber] [striplabels] [-f file]
prooftrans xml            [expand] [renumber] [striplabels] [-f file]
prooftrans ivy                     [renumner]               [-f file]
prooftrans hints [-label label] [expand]      [striplabels] [-f file]
```

Note that more than one transformation can be applied in several cases.
The option "striplabels" tells prooftrans to remove all label attributes
on clauses.

Unfortunately, the output of Prooftrans usually cannot be used as the
input to another Prooftrans job, because Prooftrans expects its input to
have specific keywords and standard-form proofs.

------------------------------------------------------------------------

### No Transformation

If no additional argument is given, Prooftrans simply extracts the proof
from the Prover9 output file.

``` my_job
prooftrans -f subset_trans.out > subset_trans.proof1
```

------------------------------------------------------------------------

### Renumber the Steps

The argument `renumber` tells Prooftrans to renumber the steps of each
proof consecutively, starting with step 1. The `expand`, `parents_only`,
and `xml` transformations can be used with the `renumber`
transformation.

``` my_job
prooftrans renumber -f subset_trans.out > subset_trans.proof2
```

------------------------------------------------------------------------

### Simplify Justifications

The argument `parents_only` tells Prooftrans list only the parents in
the justifications, not the details about inference rules or positions.
The `expand` and `renumber` transformations can be used with the
`parents_only` transformation.

``` my_job
prooftrans parents_only -f subset_trans.out > subset_trans.proof3
```

------------------------------------------------------------------------

### Expand Steps

The argument `expand` tells Prooftrans to produce more detailed proofs
in which

- all hyper- and UR-resolution steps are replaced with binary resolution
  steps,
- all demodulation sequences are replaced with paramodulation steps, and
- all unit deletion simplifications are replaced with resolution steps.

*Note to author: this is a bad example, because only one step gets
expanded.*

``` my_job
prooftrans expand -f subset_trans.out > subset_trans.proof4
```

Note that when a step is expanded (step 22 in this example), the new
steps are identified by appending 'A', 'B', etc. to the number of the
original step.

The `renumber`, `parents_only`, and `hints` transformations can be used
with the `expand` transformation.

------------------------------------------------------------------------

### XML Proofs

The options `xml` or `XML` tell Prooftrans to produce proofs in XML. The
options `expand` and `renumber` can be used with the XML transformation.

``` my_job
prooftrans xml -f subset_trans.out > subset_trans.proof5.xml
```

The preceding output is displayed by your browser not as XML, but as
some transformation of the XML, because the XML refers to an XML
stylesheet, telling the browser how to transform the XML into HTML.

To see the XML source, click "View -\> Frame Source" (or something like
that) in your browser while viewing the proof.

Here is the [DTD for Prover9 XML proofs](proof3.dtd). (If you get an
error, click "View -\> Page Source".)

------------------------------------------------------------------------

### IVY Proofs

The options `ivy` or `IVY` tell Prooftrans to produce very detailed
proofs that can be checked with the [Ivy proof
checker](http://www.cs.unm.edu/~mccune/ivy_check_prover9/).

``` my_job
prooftrans ivy -f subset_trans.out > subset_trans.proof6
```

Ivy proofs have a only 5 types of step: `input`, `propositional`,
`new_symbol`, `flip`, `instantiate`, `resolve`, and `paramod`. The
`resolve` and `paramod` do not involve unification; instances are
generated first as separate steps, and then `resolve` or `paramod` are
applied to identical atomic formulas or terms.

The Ivy proof checker cannot check steps justified by `new_symbol`.

------------------------------------------------------------------------

### Proofs to Hints

The option `hints` tells Prooftrans to take all of the proofs in the
file and produce one list of hints that can be given to Prover9 to guide
subsequent searches on related conjectures.

``` my_job
prooftrans hints -f subset_trans.out > subset_trans.proof7
```

If there is more than one proof in the file, the proofs will probably
share many steps. The list of hints that Prooftrans produces will be the
union of the steps in the proofs; that is, the duplicate steps will be
removed.

The `expand` transformation can be used with the `hints` transformation.

The label option tells prooftrans to attach label attributes to the hint
clauses. The labels consist of the string given on the command line and
a sequence number generated by prooftrans. The user's command shell may
require that the label be quoted, and if the the label is not a legal
LADR constant, prooftrans will enclose the label in double quotes.

``` my_job
prooftrans hints -label 'job8' -f subset_trans.out > subset_trans.proof8
```

------------------------------------------------------------------------

Next Section: [FOF-Prover9](fof-prover9.html)
