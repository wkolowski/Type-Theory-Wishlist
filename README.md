# Type Theory Wishlist

This repo is a playground in which I'm trying to invent a better type theory/proof assistant/dependently-typed programming language. This README describes the basic syntax and type structure of the language. Each section describes a particular feature of the language by example using concrete syntax, points to relevant papers and discusses its status (like "satndard", "prototype implemented somewhere" or "unsubstantiated speculation"). The details are laid out in subdirectories (linked to by section headers), in files with the `.ttw` extension that contain commented pseudocode which shows each feature in action. At the end we point to some ideas and TODOs for later consideration. 

## Table of Contents <a id="toc"></a>

When reading on GitHub, you can click in the upper-left corner, near the file name, for an always-up-to-date table of contents.

1. [The Guiding Principle of Syntax](#guiding-principle)
1. [Basic syntax](#basic-syntax)
1. [Types](#types)
1. [Primitive types and arrays](#primitives)
1. [Functions](#functions)
1. [Paths and the rest of Cubical Type Theory](#paths)
1. [Names and Nominal Function Type](#names)
1. [Mixed functions](#mixed-functions)
1. [Documentation comments](#doc-comments)
1. [Empty and Unit](#empty-and-unit)
1. [Records](#records)
1. [Sums](#sums)
1. [Inductive Types](#inductive-types)
    1. [Basic Inductive Types](#basic-inductive-types)
    1. [Various syntactic conveniences for inductive types](#syntactic-conveniences-for-inductives)
        1. [Constructor names may overlap between types](#non-unique-constructor-names)
        1. [The namespace associated with an inductive type](#associated-namespace)
        1. [Discriminators and the `is` syntax for single-case pattern matching](#discriminators-and-single-case-pattern-matching)
        1. [Copattern syntax for constructor arguments](#copattern-syntax-for-constructor-arguments)
        1. [Single-argument constructors](#single-argument-constructors)
        1. [Unnamed constructor arguments](#unnamed-constructor-arguments)
        1. [Syntax sugar for bundled parameters](#bundled-parameters)
    1. [Overlapping and Order-Independent Patterns](#overlapping-patterns)
    1. [Decidable Equality Patterns](#decidable-equality-patterns)
    1. [A more flexible syntax for pattern matching](#flexible-pattern-matching)
    1. [Mutual Inductive Types](#mutual-inductive-types)
    1. [Nested Inductive Types](#nested-inductive-types)
    1. [Negative Inductive Types](#negative-inductive-types)
    1. [Computational Inductive Types](#computational-inductive-types)
    1. [Higher Inductive Types](#higher-inductive-types)
    1. [Nominal Inductive Types](#nominal-inductive-types)
    1. [Inductive Families](#inductive-families)
    1. [Nested Inductive Families](#nested-inductive-families)
    1. [Syntax sugar for inductive families with uniform indices](#inductive-uniform-indices)
    1. [A more verbose (and readable) syntax for inductive types](#verbose-syntax-for-inductives)
    1. [Inductive-Inductive Types](#induction-induction)
    1. [Inductive-Recursive Types](#induction-recursion)
1. [Recursive Families](#recursive-families)
1. [Coinductive Types](#coinductive-types)
    1. [Negative Coinductive Types](#negative-coinductive-types)
    1. [Positive Coinductive Types](#positive-coinductive-types)
    1. [Various syntactic conveniences for coinductive types](#syntactic-conveniences-for-coinductives)
    1. [Nested Coinductive Types](#nested-coinductive-types)
    1. [Mutual Coinductive Types](#mutual-coinductive-types)
    1. [Coinductive Families](#coinductive-families)
    1. [Nested Coinductive Families](#nested-coinductive-families)
    1. [Syntax sugar for coinductive families with uniform indices](#coinductive-uniform-indices)
    1. [A more verbose (and readable) syntax for coinductive types](#verbose-syntax-for-coinductives)
    1. [Coinduction-Coinduction (TODO)](#coinduction-coinduction)
    1. [Coinduction-Corecursion (TODO)](#coinduction-corecursion)
1. [Mixed Inductive and Coinductive Types (TODO)](#mixed-inductive-coinductive)
    1. [Mixing records and sums: A * (B + C) = (A * B) + (A * C)](#mixing-records-and-sums)
    1. [Coinduction-Induction (TODO)](#coinduction-induction)
    1. [Types with inductive and coinductive components (TODO)](#inductive-coinductive-components)
1. [Sections and automatic abstraction over parameters](#sections)
1. [Refinement types](#refinements)
1. [Universes](#universes)
1. [Subtyping, coercions and subtype universes](#subtyping)
1. [Type-level rewriting](#type-level-rewriting)
1. [TODO: Missing features](#TODO)
    1. [List notation for `List`-like types](#list-notation)
    1. [Singleton Types](#singletons)
    1. [Generic programming](#generic)
    1. [Quantitative Type Theory](#quantities)
    1. [Graded Modalities](#graded-modalities)
    1. [Typed Holes](#holes)
    1. [Tactics](#tactics)
    1. [Metaprogramming](#metaprogramming)
    1. [Mixfix operators and notation mechanism](#notation)
    1. [Tooling](#tooling)

## The Guiding Principle of Syntax <a id="guiding-principle"></a> [↩](#toc)

The syntax of many ((dependently-typed) functional) languages is not optimal and sometimes not even good and, to be honest, the syntax of some of them (Coq) is horrible. We are not going to repeat their mistakes, however, by making use of a very simple principle used by programmers all over the world: Don't Repeat Yourself. To paraphrase: if we have to write something twice, the syntax is bad and has to be changed.

## Basic syntax <a id="basic-syntax"></a> [↩](#toc)

Comments start with `//` like in C.

```
// This is a comment.
```

Multiline comments are enclosed between ``(* *)`` like in the ML languages and can be nested.

```
(* A multiline (* nested *) comment. *)
```

Definitions are maximally uncluttered - no keywords, just a name, type and value.

```
name : type := value
```

Declarations, which at the top-level play the role of axioms, look similar but without the value part.

```
name : type
```

Directives that modify the language start with a `%`. They can be used to turn off termination checking, strict positivity, etc.

```
%NoTerminationCheck
wut : Empty := wut
```

Papers dealing with the formal treatment of definitions and declarations in PTSs:
- [Pure Type Systems with Definitions](cs.ru.nl/E.Poll/papers/dpts.pdf) - a formal treatment of definitions and `δ`-reduction
- [Pure type systems with definitions](https://pure.tue.nl/ws/files/1874317/9313025.pdf) - looks like a different (longer) version of the above
- [Parameters in Pure Type Systems](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.8.1670&rep=rep1&type=pdf)
- [Refining the Barendregt Cube using Parameters](https://www.researchgate.net/publication/2441334_Refining_the_Barendregt_Cube_using_Parameters)

TODO:
- Revisit the comment syntax.

## Types <a id="types"></a> [↩](#toc)

| Name              | Formation        | Introduction     | Elimination      |
| ----------------- | ---------------- | ---------------- | ---------------- |
| Primitive types   | `i8`, `i16`, `i32`, `i64` <br> `u8`, `u16`, `u32`, `u64` <br> `f32`, `f64` <br> `Char` <br> `Text` | literals         | primitive ops    |
| Arrays            | `Array A n`      | literals <br> library functions | `A[i]` |
| Function type     | `(x : A) -> B x` | `fun x : A => e` | `f a`            |
| Path type         | `x = y`          | `path i => e`    | `p i`            |
| Nominal function type | `∇ α : A. B α`   | `ν α : A. e`     | `t @ α`      |
| Name              | `Name A`         | with `∇` and `ν` | pattern matching |
| Empty type        | `Empty`          | impossible       | `abort`          |
| Unit type         | `Unit`           | `unit`           | not needed       |
| Record types      | `(a : A, ...)`   | `(a => e, ...)`  | `p.x`            |
| Sum types         | `[a : A, ...]`   | constructors     | pattern matching |
| Inductive types   | see below        | constructors     | pattern matching |
| Coinductive types | see below        | copattern matching | field access   |
| Refinement types  | `{x : A \| P x}` | implicit (?)     | implicit (?)     |
| Singleton types   | `Singleton A x`  | implicit (?)     | implicit (?)     |
| Strict universes  | `Type h p`       | `Type h p`       | impossible       |
| Non-strict universes | `hType h p`   | `hType h p`      | impossible       |
| Subtype universes | `Sub A`          | implicit (?)     | implicit (?)     |

## Primitive types and arrays <a id="primitives"></a> [↩](#toc)

We have a variety of primitive integer types:
- `i8`, `i16`, `i32`, `i64` - types of 8-, 16-, 32- and 64-bit signed integers, respectively
- `u8`, `u16`, `u32`, `u64` - types of 8-, 16-, 32- and 64-bit unsigned integers, respectively

We may write integer literals (both signed and unsigned) in many bases, with an underscore `_` as an optional separator used for digit grouping. To disambiguate between types when using a literal, we need a type annotation.

```
dec : i64 := 98_222
hex : i32 := 0xdeadbeef
oct : i16 := 0o77
bin : i8  := 0b1111_0000
```

There are implicit coercions between integer types provided that they do not lose information. Stated explicitly, this means there are coercions:
- from `i8` to `i16`, from `i16` to `i32`, from `i32` to `i64`
- from `u8` to `u16`, from `u16` to `u32`, from `u32` to `u64`
- from `u8` to `i16`, from `u16` to `i32` and from `u32` to `i64`

```
// Ok, `u16` values range from `0` to `65535`, which certainly fits in an `i64`.
x : i64 := 123 : u16

// Failure - there are values of type `u8`, like `255`, that don't fit into an `i8`, which ranges from `-128` to `127`. It doesn't matter that the particular value we use, i.e. `5`, is a valid value of type `i8`.
%Fail
y : i8 := 5 : u8

// To transform a value of type `u8` into a value of type `i8`, we have to use an explicit coercion. `coerce-rounding-down` casts `u8`s into `i8`s, rounding values out of range like `255` down to `127`.
z : i8 := coerce-rounding-down (5 : u8)
```

We support all the obvious arithmetical operators, including addition, subtraction, multiplication, exponentiation and division. We should also support bit-wise operations, but we're not going to see any examples.

The semantics of these operations is as usual, i.e. if the result is bigger than the maximum value for the given type, it overflows and gets cut down. For example, `255 + 1 ={u8} 0`. Division by zero is, as always, problematic... don't use it.

```
arith-example : i64 :=
  12 + (34 * 45) - 6 ^ (16 / 3)
```

The types `f32` and `f64` represent 32- and 64-bit floating point numbers, respectively, with an implicit coercion from `f32` to `f64`. We support both ordinary floating point literals and scientific notation literals and all the arithmetic operations with usual semantics.

```
almost-pi : f32 := 3.14159

big-scientific-num : f64 := 1.2345678e-9

float-expr : f64 :=
  almost-pi * 2 + big-scientific-num ^ (2 - almost-pi / 1.2e3)
```

`Char` is the type of characters. It represents UTF-8 encoded characters. Character literals are enclosed between apostrophes. We may use the usual representation of special characters (backslash followed with a letter) and quote backslashes and other special characters with an additional backslash. We support all the conventional operations on characters, including conversion to its code point, but we won't show them here.

```
char : Char := 'a'

newline : Char := '\n'

backslash : Char := '\\'
```

Strings are NOT lists of characters and they are not called "strings" so that they don't sound too familiar to people who know them from other languages. Instead there's the type `Text` which represents, well, texts, i.e. sequences of characters. Text literals are enclosed in quotes. Rules for special characters and quoting are the same as for `Char`.

```
some-text : Text := "This is a text literal."

multiline-text : Text := "This\ntext\nis\nmultiline."

quote : Text := "\"To be or not to be, that is the question.\""
```

The type `Array A n` represents arrays whose entries are of type `A` and whose length is `n : Nat`. Array literals are enclosed between `[` and `]` and separated with commas. More complicated array initializers live in the `Array` module. Array indexing syntax is similar to most C-like languages, i.e. `A[i]`. Note that `i : Fin n`, i.e. the index must be statically known to not be out of bounds.

```
arr : Array Char 5 := ['a', 'r', 'r', 'a', 'y']

an-a : Char := arr[0]

// Initialize an array with 1000 zeros.
all-zeros : Array i8 1000 := Array.repeat 0 1000

// Initialize an array with the first 25 fibonacci numbers (assuming `fib` is a
// function that computes them).
fib-arr : Array Nat 25 := Array.fromFun fib
```

We would really like to have C-like performance for base types, but this is just a wish in our Type Theory Wishlist!

Papers:
- [Primitive Floats in Coq](https://drops.dagstuhl.de/opus/volltexte/2019/11062/pdf/LIPIcs-ITP-2019-7.pdf)
- [Extending Coq with Imperative Features and its Application to SAT Verification](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.721.7071&rep=rep1&type=pdf)

Not papers:
- The workings of primitive types are borrowed from [Rust](https://doc.rust-lang.org/book/ch03-02-data-types.html)
- [Primitive objects in Coq](https://coq.inria.fr/refman/language/core/primitive.html)

**Status: some primitives types are implemented in Coq, so this shouldn't be very problematic. However, no proof assistant currently has a collection of primitive types as precise as e.g. Rust, so there will be some work to do.**

TODO:
- How does it work at the level of formal rules? Do we need zillion rules for every single primitive operation and its specification?
- Decide the details of the `Char` type.
- Decide the details of division by zero.
- We may also want to have other char types, like `Ascii` and `UTF-16`.
- Alternatively, `Char` could be made more abstract and the encoding is just its property.
- Maybe disambiguate array literal syntax from syntax sugar for lists?
- Array indexing (`a[i]`) conflicts somewhat with array literal syntax. If `a` is a function, we may interpret `a[i]` as "apply function `a` to argument `[i]`".

## Functions <a id="functions"></a> [↩](#toc)

Function types work mostly as usual, except that we want to think that all functions (including dependent ones) take just one argument which is a big (dependent) record. This view is distinct from the usual "every function takes one argument, and then maybe returns another function".

The dependent function type is written `(x : A) -> B x` and anonymous functions themselves are written `fun x : A => ...`.

```
f : (x : A) -> B x :=
  fun x : A => ...
```

We can omit the type in the `fun`, because it can be inferred from the type anyway.

```
f : (x : A) -> B x :=
  fun x => ...
```

In case `B` does not depend on `x`, we can simply write `A -> B`.

```
double : Nat -> Nat :=
  fun n : Nat => n + n
```

Function types associate to the right, i.e. `(x : A) -> (y : B) -> C x y` means `(x : A) -> ((y : B) -> C x y)`.

```
f : (x : A) -> (y : B) -> C x y :=
  fun x : A => fun y : B => ...
```

If a function takes more than one argument, we can list them all in parentheses and avoid writing the arrows in the type. We can do the same for `fun`.

```
f : (x : A, y : B) -> C x y :=
  fun (x : A, y : B) => ...
```

There's also an alternative notation which uses more parentheses, but it's discouraged (we will see one way in which its useful very soon).

```
f : (x : A) (y : B) -> C x y :=
  fun (x : A) (y : B) => ...
```

If the arguments are of the same type, we can make it even shorter.

```
f : (x y : A) -> C x y :=
  fun x y : A => ...
```

We can bind arguments together with the name, to the left of the final colon.

```
f (x y : A) : B := ...
```

There is a mechanism of implicit arguments. The syntax is inspired by [the F* language](https://www.fstar-lang.org/).

```
id (#A : Type) (x : A) : A := x
```

Of course, we can also use implicit arguments in anonymous functions.

```
id : (#A : Type, x : A) -> A :=
  fun A x => x
```

If there are many implicit arguments, like in `comp1` below, the syntax gets quite heavy. This is why we can put the arguments into groups separated by parentheses and then prefix `#` in front of a group of arguments, like in `comp2` below, which makes them all implicit at once.

```
comp1 (#A #B #C : Type, f : A -> B, g : B -> C, x : A) : C := g (f x)

comp2 #(A B C : Type) (f : A -> B, g : B -> C, x : A) : C := g (f x)
```

But then syntax gets heavy when we want to mark as implicit all argument in a group except one. In such cases, we may prefix the argument with `@` (inspired by Coq's and Haskell's syntax for explicit arguments), which overrides the group's implicitness.

```
// Function composition with the middle type (`B`) explicit.
comp3 #(A @B C : Type) (f : A -> B) (g : B -> C) (x : A) : C := g (f x)

// An equivalent but longer definition of the above.
comp3' (#A : Type) (B : Type) (#C : Type) (f : A -> B) (g : B -> C) (x : A) : C := g (f x)
```

We can omit writing implicit arguments altogether when they are easily inferable from something else. This piece of syntax is inspired by [Idris 2](https://idris2.readthedocs.io/en/latest/tutorial/typesfuns.html#implicit-arguments). We will call it "very implicit arguments". It is used pretty often in this repo, almost always with `A` and `B` standing in for types.

```
id (x : A) : A := x

comp (f : A -> B) (g : B -> C) (x : A) : C := g (f x)
```

There are also other kinds of implicitness, like looking up typeclass instances, but these are dealt with by [records](#records).

Names of functions are allowed to consist entirely of symbols, although this style is discouraged except for the most common functions, like the operators below, which are borrowed from F#: forward function application `|>` (also called "pipe forward"), backward function application `<|` (also called pipe backward), forward function composition `>>` and backward function composition `<<`.

```
(|>) (x : A) (f : A -> B) : B := f x

(<|) (f : A -> B) (x : A) : B := f x

(>>) (f : A -> B) (g : B -> C) (x : A) : C := g (f x)

(<<) (g : B -> C) (f : A -> B) (x : A) : C := g (f x)
```

There are two syntaxes for operator sections. The first one (`(* 3)` below) is borrowed from Haskell and works only for already-defined functions whose names are symbols. The second one (`(_ `mod` 2 =? 0)` below) works for any expression that represents a single-argument function, with the underscore `_` used to mark the argument. We can turn any function into an infix operator by enclosing the function's name in backticks, like for `mod` below.

Together with the pipe operators and function composition operators, this makes data processing easy and readable.

```
f0 (l : List Nat) : List Nat :=
  l |> filter (_ `mod` 2 =? 0) |> map (* 3)

// The same definition, but with desugared operator sections and desugared backticked
// functions.
f1 (l : List Nat) : List Nat :=
  l |> filter (fun n : Nat => mod n 2 =? 0) |> map (fun n : Nat => n * 3)

// The same, but using function compositions operators.
f2 (l : List Nat) : List Nat :=
  l |> (filter (not << odd) >> map (* 3))
```

Functions can be applied not only positionally, but also by naming the argument. With such application, the order of the arguments doesn't matter anymore. This is also useful when we need to explicitly provide an implicit argument.

```
self-comp (h : Nat -> Nat) : Nat -> Nat :=
  comp {A => Nat, B => Nat, C => Nat} {g => h} {f => h}
```

To reiterate: the order of arguments doesn't matter. As a bonus, we can set many arguments to the same value easily - this should be very useful easpecially for type arguments.

```
self-comp' (h : Nat -> Nat) : Nat -> Nat :=
  comp {C, A, B => Nat; f, g => h}
```

This is not the end of comfy features for functions - functions can also have default arguments!

```
// Assume for the sake of example that {} denotes text interpolation.
greet (name : Text => "World") : Text :=
  "Hello {name}!"
```

The function `greet` takes one argument `name : Text`, but we may also call it with no arguments. In such a case, `name` defaults to `"World"`.

```
Hello-Walt : Text := greet "Walt"
Hello-Walt-spec : Hello-Walt = "Hello Walt!" := refl

Hello-World : Text := greet ()
Hello-World-spec : Hello-World = "Hello World!" := refl
```

Of course anonymous function also can have default arguments.

```
greet' : (name : Text => "World") -> Text :=
  fun (name : Text => "World") => "Hello {name}!"
```

We can combine default arguments with the `Option` type (which works just like in Coq/ML/OCaml/F#) to get a nice handling of optional function arguments.

```
f : (x : A, y : Option B => None) : C := ...
```

Last but not least, there is special syntax for applying functions which have a lot of complex arguments. To apply a function `f` in this way, we write `f $` and then list the arguments below on separate lines. We can supply the arguments positionally in order and also by name, in which case they can appear out of order. This syntax is inspired by Haskell's `$` operator, and may also be used to avoid parenthesis hell when a function takes a lot of other functions as arguments.

```
complex-application
  (f : (x1 : A, x2 : B, x3 : C, x4 : D, x5 : E -> E', x6 : F, x7 : G -> G') -> X) : X :=
  f $
    arg1
    x2 => arg2
    x4 => arg4
    arg3
    fun x => ...
    arg6
    x7 => fun y => ...
```

**Status: dependent function types and dependent functions are standard, with `@` for explicit arguments and `$` for complex application being new, but very easy to implement.**

TODO:
- Figure out the precise workings of "all functions take just one argument which is a big record".
- Describe instance arguments. See Agda manual for details.
- Describe precisely how positional, named and optional arguments work when combined.

## [Path types and the rest of Cubical Type Theory](Paths) <a id="paths"></a> [↩](#toc)

We take Cubical Type Theory and the homotopical style of doing mathematics for granted. The revolution has already occurred!

In practice, this means that we have a type `I` which represents the interval. In fact `I` is only a pretype, i.e. it cannot be the codomain of a function, only the domain. There are two constants `i0 : I` and `i1 : I` which represent the beginning and the end of the inerval. There are also operations: unary `~` and binary `∧`, `∨` which together with `i0` and `i1` make `I` into a free de Morgan algebra. All the laws are computational equalities. Here's a list (taken from [Agda's documentation page](https://agda.readthedocs.io/en/v2.6.0/language/cubical.html)):

```
i0 ∨ i    ≡ i
i  ∨ i1   ≡ i1
i  ∨ j    ≡ j ∨ i
i0 ∧ i    ≡ i0
i1 ∧ i    ≡ i
i  ∧ j    ≡ j ∧ i
~ (~ i)   ≡ i
i0        ≡ ~ i1
~ (i ∨ j) ≡ ~ i ∧ ~ j
~ (i ∧ j) ≡ ~ i ∨ ~ j
```

The (homogenous) path type is written `x = y`, with the type `A` optionally appearing in braces the middle: `x ={A} y`. We should think that a path `p : x = y` is a function `f : I -> A` such that `f i0` computes to `x` and `f i1` computes to `y`.

There's also the heterogenous path type `x == y` (more explicitly written `x ={i.A} y`), in which `A : I -> Type` is a "line of types", i.e. a family of types that depends on an interval variable. In this case, we think that a heterogenous path `p : x == y` is a dependent function `f : (i : I) -> A i` such that `f i0` computes to `x` and `f i1` computes to `y`.

To introduce a path `x = y` we use a lambda-like binding construct `path i => e`, where `e[i => i0]` must be computationally equal to `x` and `e[i => i1]` must be computationally equal to `y`.

```
refl (x : A) : x = x :=
  path i => x
```

To eliminate a path, we apply it like an ordinary function.

```
sym #(x y : A) (p : x = y) : y = x :=
  path i => p (~ i)
```

With cubical path types, we can easily prove that paths between functions are homotopies.

```
funExt #(f g : A -> B) (p : (x : A) -> f x = g x) : f = g :=
  path i => fun x : A => p x i
```

The syntax may get somewhat heavy when we mix paths and functions frequently, so we have a shorthand (which is even shorter than the original `fun`!).

```
funExt #(f g : A -> B) (p : (x : A) -> f x = g x) : f = g :=
  \i x => p x i
```

But sometimes even that is too long. In such cases we may want to use `ap`.

```
ap (f : A -> B) #(x y : A) (p : x = y) : f x = f y :=
  path i => f (p i)
```

Our paths enjoy some nice computational equalities.

```
sym-sym #(x y : A) (p : x = y) : sym (sym p) = p := refl

ap-id #(x y : A) (p : x = y) : ap (fun x => x) p = p := refl

ap-ap #(A B C : Type) #(x y : A) (f : A -> B) (g : B -> C) (p : x = y)
  : ap g (ap f p) = ap (f >> g) p := refl
```
There's more to discuss, like transport, partial elements, generalized composition and so on, but we'll leave the discussion of Cubical Type Theory at this point. In case of doubt, refer to [Cubical Agda's documentation page](https://agda.readthedocs.io/en/v2.6.2/language/cubical.html)

Main paper:
- [Cubical Type Theory: a constructive interpretation of the univalence axiom](https://arxiv.org/pdf/1611.02108.pdf)

Lesser papers:
- [Towards a cubical type theory without an interval](https://akaposi.github.io/towards_a_cubical_tt_without_interval.pdf)
- [Canonicity for Cubical Type Theory](https://link.springer.com/article/10.1007/s10817-018-9469-1)
- [MODELS OF HOMOTOPY TYPE THEORY WITH AN INTERVAL TYPE](https://arxiv.org/pdf/2004.14195.pdf)
- [Normalization for Cubical Type Theory](https://www.jonmsterling.com/pdfs/cubical-norm.pdf)

Slides:
- [Objective Metatheory of (Cubical) Type Theory](http://www.jonmsterling.com/pdfs/proposal-slides.pdf)
- [Unifying Cubical Models of Homotopy Type Theory](https://www.uwo.ca/math/faculty/kapulkin/seminars/hottestfiles/Mortberg-2019-10-23-HoTTEST.pdf)

Prototypes:
- [cubicaltt](https://github.com/mortberg/cubicaltt)
- [anders](https://github.com/groupoid/anders)
- [yactt](https://github.com/mortberg/yacctt)
- [mlang](https://github.com/molikto/mlang)
- [smalltt](https://github.com/AndrasKovacs/smalltt) - not actually cubical, but only ordinary MLTT, but worth taking a look because it's fast

**Status: there are some papers which describe Cubical Type Theory in great detail and there are prototype implementations based on these papers.**

TODO:
- Refresh my knowledge of and then master the machinery behind Cubical Type Theory (systems, Glue, etc.)
- Describe these things here.

## Names and Nominal Function Type <a id="names"></a> [↩](#toc)

For every type `A` there is a type `Name A` whose elements can be thought of as "names for elements of `A`". There's also the nominal function type `∇ α : A. B` which expresses the idea of an element of `B` that may use the bound name `α : Name A` for an element of type `A`. The nominal function type `∇ α : A. B` is sometimes also called the nabla type, due to the notation. I don't yet have a good name for this type, but maybe we should use "nominal abstraction type"?

Anyway, terms of the nominal function type `∇ α : A. B` are introduced with a nominal abstraction `ν α : A. b` where `b : B` is a term that may use `α : Name A`. Note that in the nominal abstraction we gave the "type annotation" `α : A`, but this means that `α` is a NAME for an element of type `A`, so in fact `α` is of type `Name A`. We may also omit the annotation and write simply `ν α. b`. Customarily we use lowercase greek letters for names.

What is the intuitive meaning of nominal abstraction? It captures all the key properties of name-binding, namely (these are taken from the CNIC paper):
- Freshness: The name introduced by nominal abstraction is distinct from any names bound outside the given binding. For example, given the term `ν α. ν β. t` inside the term `t` the names `α` and `β` are distinct.
- α-equivalence: Terms with name-bindings are equal up to renaming of bound names. For example, `ν α. α` is equal to `ν β. β`.
- Scoping: A name cannot occur outside a binding for it. For example, `α` is a valid term only under a binding `ν α. ...`. Note that this doesn't mean that we rule out "open terms" - we may consider open terms in some scope when their free variables are bound in an enclosing scope.
- Typing: Different types of names can be bound. For example, when formalizing System F, names for term and type variables are of distinct type.

Nominal functions can be eliminated using concretion operation: given `t : ∇ α : A. B` and `β : A` which is fresh for `t`, we have `t @ β : B[α := β]` with the computation rule `(ν α. b) @ β ≡ b[α := β]`. We also have the uniqueness rule: given `t : ∇ α : A. B`, we have `t ≡ ν α. t @ α`.

The main use of names and the nominal function type is together with inductive types, to represent name binding in the syntax of programming languages, logics, calculi and so on, where they effectively implement the "Barendregt convention". See the section on [Nominal Inductive Types](#nominal-inductive-types) for more. However, they can also be used with coinductive types and with whatever other feature our language has - I guess that interactions between many of them and nominal features are not yet discovered!

Papers:
- [The Calculus of Nominal Inductive Constructions](https://homepage.divms.uiowa.edu/~astump/papers/cinic-lfmtp09.pdf)
- [A Dependent Type Theory with Abstractable Names](https://www.sciencedirect.com/science/article/pii/S1571066115000079)

Note: so far, our nominal features are based on the first of these papers, i.e. the Calculus of Nominal Inductive Constructions. There are some reasons to think that the second paper may present a better system, but so far I haven't been able to decipher it on an intuitive level.

**Status: prototype implemented for CNIC, but long ago (and with Lisp syntax, lol). Prototype implemented for FreshMLTT, but it looks bad. No proof whether FreshMLTT has decidable typechecking.**

TODO:
- Find a better name for the nominal function type. Maybe "nominal abstraction type".
- Figure out how the paper "A Dependent Type Theory with Abstractable Names" works at an intuitive level.

## Mixed functions <a id="mixed-functions"></a> [↩](#toc)

As you have noticed by now, we have three function-type-like types: the actual function type, the path type and the nominal abstraction type. Since we may sometimes want to mix them (a function which returns a path between nominal functions which return a function... and so on), we have a special uniform notation for this case.

As a showcase, we will prove extensionality of nominal functions.

```
nominal-funext :
  (#A : Type, #B : A -> Type, f g : ∇ α : A. B α, H : ∇ α : A. f @ α = g @ α) -> f = g :=
    \A B f g H i 'α => H @ α i
```

Instead of the previously seen `fun`, `path` and `ν`, we now have a single abstraction operation written `\`, like in Haskell. In this syntax ordinary function arguments and path arguments are written as usual, whereas name arguments are written with an apostrophe at the front, like type variables in ML. This marking is necessary - if we don't write it, the thing will be interpreted as an ordinary function that takes an argument of type `Name _`.

At the type level, we can use double backslash `\\` to denote mixing of ordinary and nominal function types (the names also need to be marked with an apostrophe). For example, `\\(A : Type, 'α : A) -> B α` means `(A : Type) -> ∇ α : A. B α`. If we wanted a normal function that takes a name, we would write `\\(A : Type, α : Name A) -> B α`, which is interpreted as `(A : Type) -> (α : Name A) -> B α`.

As for application of such mixed functions, it is written like ordinary function application - `(\n : Nat => n + n) 5` is the same as `(fun n : Nat => n + n) 5`, whereas `(\'α : A => ...) β` is the same as `(ν α : A. => ...) @ β`.

**Status: not sure, but I think Agda allows mixing ordinary functions with paths. Anyway, this is very easy to implement.**

TODO:
- Reconsider the syntax.

## Documentation comments <a id ="doc-comments"></a> [↩](#toc)

Our language has very powerful documentation comments, a feature borrowed from [the Union language](https://www.unisonweb.org/docs/documentation/).

Doc comments are first class, which means that there's a type `Doc` whose values are doc comments. This type is recursive, so we can embed docs in other docs. We can also include typechecked code snippets in docs and have them evaluated inline.

Docs comment blocks are enclosed between `{{` and `}}`. This syntax creates an expression of type `Doc` - remember, doc comments are first-class. The basic syntax of doc comments is Markdown-like.

```
doc-comment : Doc :=
{{
  This is a doc comment. I like trains. Trains like me, too.

  The basic syntax is markdown-like. We can _underline_ words, make them **bold** or
  ~~strike them through~~.

  Here's a numbered list:
  1. First item.
  1. Second item - note the 1. at the beginning, numeration is automatic.
  1. Third item.

  Here's an unnumbered list:
  - The Good
  - The Bad
  - The Ugly

  We can make tables:

  | First column | Second column |
  | ------------ | ------------- |
  | nananananana | BATMAN        |

  We can make [links](https://www.wecanmakelinks.com)
}}
```

We don't need to bind doc comments to variables. We can create them anonymously by placing them just before the definition to which theey pertain. The code below results in two new definitions, `five : Nat` and `five.doc : Doc`.

```
{{Five is a very important number. Trust me, I'm a mathematician.}}
five : Nat := 5
```

We can read docs in the REPL by using the command `:docs name`. This command will look for a term called `name.doc` of type `Doc` and display it if it is found.

```
> :check five
five : Nat

> :print five
five : Nat := 5

> :docs five

Five is a very important number. Trust me, I'm a mathematician.
```

We can use double backticks ` `` ` to refer to a previously defined value. If there's nothing with this name or there is more than one definition with this name, we will get an error. We can use triple backticks ` ``` ` to evaluate a term. In the resulting `Doc`, this term will be replaced with its value.

Moreover, we can write `@def{term}` to inline the definition of a term and `@type{term}` to inline the type of a term.

```
{{
  @type{id}

  ``id`` is the identity function which does nothing (or, at least, nothing interesting).

  Full definition: @def{id}

  Examples:
  - ``id 42`` evaluates to ```id 42```
  - ``id "WUT"`` evaluates to ```id "WUT"```
}}
id (#A : Type, x : A) : A := x
```

In the REPL, asking for the docs will result in

```
> :docs id

id : (#A : Type, x : A) -> A

`id` is the identity function which does nothing (or, at least, nothing interesting).

Full definition: id := fun (#A : Type, x : A) => x

Examples:
- `id 42` evaluates to `42`
- `id "WUT"` evaluates to `"WUT"`
```

We don't need to write one big doc comment at a time - we can split doc comments into subdocs and them include them in the main doc comment. Let's see how to write the above doc comment for `id` in this way.


```
{{
  {{ id.doc.type }}

  {{ id.doc.text }}

  {{ id.doc.def }}

  {{ id.doc.ex }}
}}
id (#A : Type, x : A) : A := x

id.doc.type : Doc :=
  {{ @type{id} }}

id.doc.text : Doc :=
  {{ ``id`` is the identity function which does nothing (or, at least, nothing interesting). }}

id.doc.def : Doc :=
  {{ Full definition: @def{id} }}

id.doc.ex : Doc :=
{{
  Examples:
  - ``id 42`` evaluates to ```id 42```
  - ``id "WUT"`` evaluates to ```id "WUT"```
}}
```

In the REPL, this results in the same result as before.

```
> :docs id

id : (#A : Type, x : A) -> A

`id` is the identity function which does nothing (or, at least, nothing interesting).

Full definition: id := fun (#A : Type, x : A) => x

Examples:
- `id 42` evaluates to `42`
- `id "WUT"` evaluates to `"WUT"`
```

**Status: Unison has it, so it's doable.**

TODO:
- I'm not yet sure whether the dot in `five.doc` is just a part of an ordinary name or whether it has something to do with namespacing. I'll decide later.

## `Empty` and `Unit` <a id="empty-and-unit"></a> [↩](#toc)

There's the built-in `Empty` type which has no terms in the empty context. Its eliminator is called `abort`.

```
abort : Empty -> A
```

`abort` is a coercion, so we don't need to write it explicitly.

```
abort-coercion (e : Empty) : A := e
```

`Empty` is a strict proposition, i.e. all its proofs are computationally equal.

```
StrictProp-Empty (e1 e2 : Empty) : e1 = e2 := refl
```

There's also the built-in `Unit` type. Its sole term is called `unit`.

```
unit : Unit
```

There's no need for an elimination principle for `Unit`, because, just like `Empty`, it is a strict proposition, i.e. all terms of type `Unit` are computationally equal.

```
StrictProp-Unit (u1 u2 : Unit) : u1 = u2 := refl
```

Relevant papers:
- [Definitional Proof-Irrelevance without K](https://hal.inria.fr/hal-01859964v2/document)

**Status: `Empty` and `Unit` are standard everywhere, but barely anywhere are they strict propositions. Coq and Agda have implemented universes of strict propositions (impredicative and predicative) based on the above paper. The paper proves that the theory is consistent, compatible with univalence, and has decidable typechecking. Overall, this looks very doable.**

## [Records (and sums)](Records) <a id="records"></a> [↩](#toc)

Record types are the central feature of the language and they subsume modules, typeclasses, sigma types, product types, and so on. This even extends to packaging constructs - our records are supposed to be "on the same level" as Java's packages or Rust's crates. Let's start our journey into the land of records with some motivation, by describing what we want to achieve.

### Some problems with records found in Coq (and most other languages)

1. Besides records we have typeclasses with instance search, modules which are even more second-class than records, and sigma types which are just annoying. Additionally, in the metatheory we also have contexts, which are basically just another form of records. Moreover, record definitions are pretty similar to definitions of (non-inductive) sums, inductives and coinductives, in the sense that all of these are just a bunch of `name : type` declarations.
1. Record field names must be globally unique. This is very annoying in Haskell and Coq, but probably easy to solve and not present in other languages.
1. No definitional uniqueness principle for records in most languages. This is solved in Agda, however.
1. Hard to prove record equality. This is very annoying in Coq, but probably much easier when we have Cubical Type Theory and path types.
1. Hard to reuse record types. For example, when we have record types that represent reflexive, symmetric and transitive relations, they aren't very helpful when defining a record type for equivalence relations - if we try to reuse them, we'll get a subpar solution.
1. Telescopization stemming from lack of inheritance. In an extreme version of the algebraic hierarchy, a group is a monoid with inverse, and a monoid is a pointed semigroup with laws, and a semigroup is an associative magma and so on. Defining a group then requires unwinding all these telescopes, which is unwieldy.
1. Hard to unbundle records into typeclasses (i.e. turn a `Monoid` into an instance of `Monoid A` for some carrier `A`) and hard to bundle classes into records (i.e. turn an instance of `Monoid A` into a `Monoid` whose carrier is `A`).
1. This is not directly about records, but it's sometimes hard to do currying of functions that take many arguments. Records could help wiht that, but they don't, because we don't have any notion of "partial application" for records.

### How records work

We have three distinct but equivalent syntaxes for records, called the tuple syntax, the copattern syntax and the module syntax. They can be also called the short, medium and long syntaxes, respectively. The tuple syntax is the most compact and best suited for passing data around. The copattern syntax is of medium size and best suited to defining functions operating on records. The module syntax is the most verbose and best suited to, well... tasks that have to do with modularity.

### Tuple syntax

In the tuple syntax, we use parentheses for both record types and records themselves.

```
point : (x : Nat, y : Nat, z : Nat) :=
  (0, 42, 111)
```

Tuples are inherently named - when creating them we may freely use field names.

```
point : (x : Nat, y : Nat, z : Nat) :=
  (x => 0, y => 42, z => 111)
```

We can put field names of the same type next to each other without repeating the type.

```
point : (x y z : Nat) :=
  (x => 0, y => 42, z => 111)
```

We can use this syntax also for records, when many fields are going to have the same value.

```
origin : (x y z : Nat) :=
  (x, y, z => 0)
```

We can access record fields with dot syntax.

```
point-x : Nat := point.x
```

An example function on records that translates a 3D point in the x-dimension.

```
translateX (n : Nat) (p : (x y z : Nat)) : (x y z : Nat) :=
  (x => p.x + n, y => p.y, z => p.z)
```

We can avoid repeating the name of the record by using the `open` syntax which makes all fields of the record available in the context.

```
translateX (n : Nat) (p : (x y z : Nat)) : (x y z : Nat) :=
  open p in (x => x + n, y => y, z => z)
```

If that's still too long, rest assured: function arguments which are records are `open`ed automatically for us! So we only need to use field names qualified with the record name to disambiguate in case of name clashes.

```
translateX (n : Nat) (p : (x y z : Nat)) : (x y z : Nat) :=
  (x => x + n, y => y, z => z)
```

There's the record update syntax, which we will call prototyping. When we define a record using the prototype `p`, all fields of the new record that are not explicitly given will be the same as in `p`.

```
translateX (n : Nat) (p : (x y z : Nat)) : (x y z : Nat) :=
  (x => p.x + n, _ => p)
```

When using prototyping, we can also use `$=>` to modify a field instead of just setting it. Maybe this will save us some writing for records with long names and field names.

```
translateX (n : Nat) (p : (x y z : Nat)) : (x y z : Nat) :=
  (x $=> (+ n), _ => p)
```

### Copattern syntax


In copattern syntax, we put each field definition in a separate line that starts with an `&`.
```
point : (x y z : Nat)
& x => 0
& y => 42
& z => 111
```

If multiple fields have the same value, we can define all of them at once. We call these _and-copatterns_, in analogy with the more established or-patterns from ML.

```
origin : (x y z : Nat)
& x & y & z => 0
```

Of course we don't need to write all of them in a single line.

```
origin : (x y z : Nat)
& x
& y
& z => 0
```

This is how `translateX` looks in copattern syntax.

```
translateX (n : Nat) (p : (x y z : Nat)) : (x y z : Nat)
& x => p.x + n
& y => p.y
& z => p.z
```

Just like for tuple syntax, we can use `open` to open a record...

```
translateX (n : Nat) (p : (x y z : Nat)) : (x y z : Nat)
open p in
& x => x + n
& y => y
& z => z
```

... but just like for tuple syntax, we don't need it, because it is opened automatically for us.

```
translateX (n : Nat) (p : (x y z : Nat)) : (x y z : Nat)
& x => x + n
& y => y
& z => z
```

Copatterns can use prototypes too!

```
translateX (n : Nat) (p : (x y z : Nat)) : (x y z : Nat)
& _ => p
& x => p.x + n
```

Copatterns also allow the modify syntax.

```
translateX (n : Nat) (p : (x y z : Nat)) : (x y z : Nat)
& _ => p
& x $=> (+ n)
```

### Module syntax

The module syntax is lengthy, but offers lots of freedom. In the module below, the fields `y-aux` and `garbage` will be ignored, even though we may use them (but don't need to) to define other fields' values.

```
point : (x y z : Nat) :=
module

  x : Nat => 0

  y-aux : Nat => 21

  y : Nat => 2 * y-aux

  z : Nat => 111

  garbage : Text => "not a field - the only fields are x, y and z"

end
```

Multiple fields of the same type can be declared/defined more compactly.

```
origin : (x y z : Nat) :=
module
  x y z : Nat => 0
end
```

Yes, we can use module syntax to define functions! But don't do that - it's verbose and it's better to just use the copattern syntax.

```
translateX (n : Nat) (p : (x y z : Nat)) : (x y z : Nat) :=
module
  x : Nat => p.x + n
  y : Nat => p.y
  z : Nat => p.z
end
```

We have the `open` syntax that we can use just like before...

```
translateX (n : Nat) (p : (x y z : Nat)) : (x y z : Nat) :=
  open p in
module
  x : Nat => x + n
  y : Nat => y
  z : Nat => z
end
```

... but we can also put the `open` inside the module.

```
translateX (n : Nat) (p : (x y z : Nat)) : (x y z : Nat) :=
module
  open p

  x : Nat => x + n
  y : Nat => y
  z : Nat => z
end
```

Just like before, we don't need the `open` keyword, because record arguments are opened automatically.

```
translateX (n : Nat) (p : (x y z : Nat)) : (x y z : Nat) :=
module
  x : Nat => x + n
  y : Nat => y
  z : Nat => z
end
```

Modules can use prototyping too, but this time we should put them at the top of the module.

```
translateX (n : Nat) (p : (x y z : Nat)) : (x y z : Nat) :=
module
  prototype p

  x : Nat => p.x + n
end
```

The modify syntax also works with modules - no surprise there.

```
translateX (n : Nat) (p : (x y z : Nat)) : (x y z : Nat) :=
module
  prototype p

  x : Nat $=> (+ n)
end
```

### Record types with manifest fields

Our record types can have some fields set in advance, like the following type of points that have `x`, `y` and `z` coordinates, but the `z` coordinate is set to `0`. To distinguish these record types from record, we use `:=` to denote the value of a field, not `=>`.

```
p : (x y : Nat, z : Nat := 0) := (x => 1, y => 2)
```

We can access `z` even though we didn't explicitly set it.

```
p-z : Nat := p.z
```

In fact, when setting a field, we can reflect the change in the type of the result.

```
translateX (n : Nat) (p : (x y z : Nat)) : (x : Nat := p.x + n, y z : Nat) :=
  (x => p.x + n, _ => p)
```

Because we already wrote it at the type level, we may omit it at the term level.

```
translateX (n : Nat) (p : (x y z : Nat)) : (x : Nat := p.x + n, y z : Nat) :=
  (_ => p)
```

### Operations on record types

Given a record type, we can rename its fields to get another record type.

```
example-rename-1 :
  (x y z : Nat) renaming (x to a) = (a y z : Nat) := refl
```

We can rename multiple fields at once.

```
example-rename-2 :
  (x y z : Nat) renaming (x to a, y to b, z to c) = (a b c : Nat) := refl
```

Renaming also works on manifest fields.

```
example-rename-3 :
  (x y : Nat, z : Nat := 0) renaming (z to w) = (x y : Nat, w : Nat := 0) := refl
```

Renaming a field on which another depends is also permitted.

```
example-rename-4 :
  (outl : A, outr : B outl) renaming (outl to fst, outr to snd)
    =
  (fst : A, snd : B fst)
    := refl
```

We can set a field to the given value.

```
example-set-1 :
  (x y z : Nat) setting (z := 0) = (x y : Nat, z : Nat := 0) := refl
```

We can also unset a field.

```
example-unset-1 :
  (x y : Nat, z : Nat := 0) unsetting z = (x y z : Nat)
```

We can remove a field to get a new record type.

```
example-removing : (x y z : Nat) removing z = (x y : Nat) := refl
```

Record types can be joined together. By "join" we mean a kind of non-disjoint union or pushout - fields which have the same names are collapsed into one, and those that have different names remain separate. In case there are two fields with the same names but different types, the join is illegal.

```
example-join-1 : (outl : A) & (outr : B) = (outl : A, outr : B) := refl
```

We can also combine record types dependently.

```
example-join-2 : (outl : A) & (outr : B outl) = (outl : A, outr : B outl) := refl
```

We can join records with clashing field names, provided that they are of the same type.

```
example-join-3 : (x y : Nat) & (y z : Nat) = (x y z : Nat) := refl
```

The join operation preserves implicitness of arguments.

```
example-join-4 : (#outl : A) & (outr : B outl) = (#outl : A, outr : B outl) := refl
```

We can combine joins, renaming, setting, unsetting and removing into a single operation. This way we can create a new record type from a given prototype record type.

```
example-prototyping :
  (x y : Nat, z : Nat := 0, n : Nat) with (x to a := 5, y to b, unset z, remove n)
    =
  (a : Nat := 5, b z : Nat)
    := refl
```

Armed with such nice records, we can solve the problem that were posed at the beginning of this section.

### Problem 1: globally unique field names

Record field names need not be globally unique. In case they clash, we can disambiguate manually.

Note: for now, we use `RType` to denote the universe of record types.

```
Point2D : RType := (x y : Nat)
Point3D : RType := (x y z : Nat)

// In the REPL:
> :check x
> Point2D.x : Point2D -> R
> Point3D.x : Point3D -> R
```

We also have some facilities for dealing with name clashes in other situations.

```
// Loooooooooong!
dist1 (p : (x y z : Nat)) : Nat :=
  sqrt (p.x * p.x + p.y * p.y + p.z * p.z)
```

We can use the syntax `open p` to make all field of `p` accessible.

```
dist2 (p : (x y z : Nat)) : Nat :=
  open p in sqrt (x * x + y * y + z * z)
```

But we can `open` the record implicitly if there are no naming conflicts.

```
dist3 (p : (x y z : Nat)) : Nat :=
  sqrt (x * x + y * y + z * z)
```

And even if there are conflicts, we may still open all records and resolve the name clashes explicitly.

```
bogus (p : (x y z : Nat)) (q : (z w : Nat)) : Nat :=
  x + y + p.z + q.z + w
```

### Problem 2: no definitional uniqueness principle for records

Records do have a definitional uniqueness principle!

```
definitional-uniqueness-for-records
  (r : (a : A, b : B a)) : r = (a => r.a, b => r.b) := refl
```

There's also a uniqueness principle for prototypes.

```
uniqueness-principle-for-prototypes
  (r : (a : A, b : B a)) : r = (_ => r) := refl
```

### Problem 3: hard to prove record equality

With path types and other cubical features, proving record equality is easy enough.

```
path-point3D #(a b : (x y z : Nat))
  (px : a.x = b.x, py : a.y = b.y, pz : a.z = b.z) : a = b :=
    path i => (x => px i, y => py i, z => pz i)
```

### Problem 4: hard to reuse record types

Let's define record types that represent reflexive, symmetric and transitive relations. We can do that not only in tuple syntax, but also in copattern syntax.

```
Refl : RType
& A : Type
& R : A -> A -> Prop
& reflexive : (x : A) -> R x x

Sym : RType
& A : Type
& R : A -> A -> Prop
& symmetric : (x y : A) -> R x y -> R y x

Trans : RType
& A : Type
& R : A -> A -> Prop
& transitive : (x y z : A) -> R x y -> R y z -> R x z
```

We can use the join operation to combine `Refl`, `Sym` and `Trans` into `Equiv`, which represents the type of equivalence relations.

```
Equiv : RType := Refl & Sym & Trans
```

The above join is equal to the manually encoded record type that represents equivalence relations.

```
Equiv' : RType
& A : Type
& R : A -> A -> Prop
& reflexive : (x : A) -> R x x
& symmetric : (x y : A) -> R x y -> R y x
& transitive : (x y z : A) -> R x y -> R y z -> R x z

Equiv-is-Refl-Sym-Trans :
  Equiv = Equiv' := refl
```

### Problems 5: telescopization stemming from lack of inheritance

We can also use record types as prototypes to construct other record types. First let's define `Magma`s, i.e. binary operations together with their carrier, and `Pointed` types, i.e. a pair that consists of a type and a term of that type.

```
Magma : RType
& A : Type
& op : A -> A -> A

Pointed : RType
& A : Type
& point : A
```

A `Semigroup` is a magma whose operation is associative. To define `Semigroup`, we (dependently!) join `Magma` with a single-field record that represents associativity of `op`.

```
Semigroup : RType :=
  Magma &
  (assoc : (x y z : A) -> op (op x y) z = op x (op y z))
```

We can also do this in copattern syntax - here inheritance is denoted with `$`.

```
Semigroup : RType
$ Magma
& assoc : (x y z : A) -> op (op x y) z = op x (op y z)
```

We can now define `Monoid` by joining `Semigroup`, `Pointed` and adding the other required laws by hand. Note that can rename fields during the join.

```
Monoid : RType 
$ Semigroup
$ Pointed renaming point to id
& idl : (x : A) -> op id x = x
& idr : (x : A) -> op x id = x
```

The type of `Monoid`s defined in this way is computationally equal to the below one, defined manually.

```
Monoid' : RType
& A : Type
& op : A -> A -> A
& assoc : (x y z : A) -> op (op x y) z = op x (op y z)
& id : A
& idl : (x : A) -> op id x = x
& idr : (x : A) -> op x id = x

Monoids-same : Monoid = Monoid' := refl
```

### Problem 6: hard to unbundle record types into typeclasses

We can easily obtain a typeclass by setting a field in the `Monoid` type. For now, we ignore the matter of what a typeclass is.

```
MonoidClass (A : Type) : RType :=
  Monoid setting A to A
```

This is the result of the above definition written more explicitly.

```
MonoidClass' (A : Type) : RType
& op : A -> A -> A
& assoc : (x y z : A) -> op (op x y) z = op x (op y z)
& id : A
& idl : (x : A) -> op id x = x
& idr : (x : A) -> op x id = x

MonoidClass-MonoidClass' : MonoidClass = MonoidClass' := refl
```

We can also reverse these operations and bundle MonoidClass' to get a record type.

```
Monoid' : RType
& A : Type
&& MonoidClass' A

Monoid-Monoid' : Monoid = Monoid' := refl
```

### Problem 7: currying/uncurrying of functions and the relationship between records and function arguments

Since we have implicit record opening and don't use the bound variable `p` at all, maybe we shouldn't need to write it?

```
dist4 (x y z : Nat) : Nat :=
  sqrt (x * x + y * y + z * z)
```

The only difference between `dist1`-`dist3` and `dist4` is that the former's arguments are collected into a record, while the latter's are not.

Let's see in the repl:

```
> :check dist1
> dist1 : (p : (x y z : Nat)) -> Nat

> :check dist2
> dist2 : (p : (x y z : Nat)) -> Nat

> :check dist3
> dist3 : (p : (x y z : Nat)) -> Nat

> :check dist4
> dist4 : (x y z : Nat) -> Nat
```

We can convert between these two representations (arguments collected into a record and freestanding arguments) using the currying/uncurrying operator `&`.

```
> :check &dist1 : (x y z : Nat) -> Nat
> :check &dist4 : (dist4-args : (x y z : Nat)) -> Nat

// We thus have the obvious equalities.
dist1-dist4 : dist1 = &dist4 := refl
dist4-dist1 : &dist1 = dist4 := refl
```

### Summary

[Here](Records/TurboRecords.ttw) you can find a wilder and more ambitious idea of what records should be.

Papers on dependent records in type theory:
- [Dependent Record Types Revisited](http://www.cs.rhul.ac.uk/home/zhaohui/DRT11.pdf)
- [Typed Operational Semantics for Dependent Record Types](http://www.cs.rhul.ac.uk/home/zhaohui/TYPES09final11-01-01.pdf)
- [Ur: Statically-Typed Metaprogramming with Type-Level Record Computation](http://adam.chlipala.net/papers/UrPLDI10/UrPLDI10.pdf)

Older papers:
- [Extension of Martin-Löf 's Type Theory with Record Types and Subtyping](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.49.5862&rep=rep1&type=pdf)
- [Dependently Typed Records in Type Theory](https://sci-hub.se/10.1007/s001650200018) (also see [Agda code](https://agda.github.io/agda-stdlib/Data.Record.html) based on the paper)
- [Dependently Typed Records for Representing Mathematical Structure](https://sci-hub.se/10.1007/3-540-44659-1_29)
- [A Logical Framework with Dependently Typed Records](https://www.researchgate.net/publication/226374245_A_Logical_Framework_with_Dependently_Typed_Records)
- [Algebraic Structures and Dependent Records](https://www.researchgate.net/publication/242555886_Dependent_record_types_and_algebraic_structures_in_type_theory)

Papers on extensible records:
- [Abstracting Extensible Data Types: Or, Rows by Any Other Name](https://www.pure.ed.ac.uk/ws/portalfiles/portal/87175778/Abstracting_extensible_data_types_MORRIS_DoA_tbc_VoR_CC_BY.pdf)

Papers on manifest fields:
- [Manifest types, modules, and separate compilation](https://www.cs.tufts.edu/~nr/cs257/archive/xavier-leroy/105.pdf)
- [Manifest Fields and Module Mechanisms in Intensional Type Theory](http://www.cs.rhbnc.ac.uk/home/zhaohui/Modules08.pdf)

Other papers:
- [Functions, Records and Compatibility in the λN Calculus](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.1046.5339&rep=rep1&type=pdf) - also describes functions with named arguments
- [Theories as Types](https://kwarc.info/people/frabe/Research/MRK_modelsof_18.pdf)
- [Dependent Intersection: A New Way of Defining Records in Type Theory](https://www.cs.cornell.edu/people/kopylov/papers/dinter/dinter.pdf)
- [A Type-Theoretic Approach to Higher-Order Modules with Sharing](https://www.cs.tufts.edu/~nr/cs257/archive/modules/p123-harper.pdf)

Papers on type classes:
- [Type Classes for Mathematics in Type Theory](https://arxiv.org/pdf/1102.1323.pdf)
- [First-Class Type Classes](https://sozeau.gitlabpages.inria.fr/www/research/publications/First-Class_Type_Classes.pdf)
- [Modular Type Classes](https://www.cs.cmu.edu/~rwh/papers/mtc/short.pdf)
- [Modular implicits](https://www.cl.cam.ac.uk/~jdy22/papers/modular-implicits.pdf)

**Status: mostly wild speculations. The papers promise much, but no good implementations/prototypes, so probably there's something wrong with them.**

TODO:
- Finish thinking about records.
- How to turn typing contexts into record types? This would free us from some duplication at the meta level. But beware! This is not the same idea as "first-class typing contexts" and certainly not the same as "first-class evaluation contexts".
- Rethink modify syntax for modules.
- Rethink whether the prototype should really go at the end of the record definition.
- Deduplicate explanations of `open` syntax in the first three sections and then in Problem 1 section.
- How exactly do dependent records work? We need more examples.
- Discuss the sort (i.e. universe) of record types and how to declare record types.
- Discuss implicit record fields.
- How to avoid the ugly `A setting x to x` thing? Maybe `A @x` for passing implicit arguments?
- Rethink whether `$` is a good syntax for record type prototyping. Make sure it does not collide with `$=>` and with `$` used for complex function application.
- Decide whether prototype copatterns should be at the beginning or at the end.
- Rethink `RType` and how to make records first-class.
- Add a term-level `removing` operation.
- Make sure that copatterns and the built-in stuff make optics absolutely unneeded. Having to know profunctors just to peek at record fields is bad.

## Sums <a id="sums"></a> [↩](#toc)

We have extensible sum types. This means that we can create sum types on the go, without having to declare them beforehand, and then we can use them as if they were ordinary sum types.

Extensible sums are written in a notation similar to records, but using square brackets. Constructors are written as `name of argType`.

```
sum (A B : Type) : Type := [inl of A, inr of B]

x : sum Nat Bool := inl 5
y : sum Nat Bool := inr ff
```

Alternatively, constructors can take records as arguments, and the syntax is

```
Sum (A B : Type) : Type := [inl (l : A), inr (r : B)]

// Argument given explicitly as a record.
x : Sum Nat Bool := inl (l => 5)

// Argument given positionally.
x : Sum Nat Bool := inl 5
```

The dual of the records' join operator `&` is the sums' union operator `|`. If the arguments of `|` share no fields, then the result is a disjoint sum.

```
sum3 : [inl of A, inr of B, orc of C] = sum A B | [orc of C] := refl
```

If the arguments of `|` share fields of the same name and type, they are merged in a pushout-like manner.

```
sum' (A B : Type) : Type := [inr of A, orc of B]

sum3' : [inl of A, inr of B, orc of C] = sum A B | sum' B C := refl
```

If the arguments of `|` share fields of the same name but different type, this is an error.

```
// The error is something like "cannot union field `inl of A` with field `inl of B`.
%Fail
wut : Type := sum A B | sum B A
```

For enumerations, we don't need to write the argument type.

```
color : Type := [R, G, B]
```

We have a shorthand syntax for multiple constructors with the same arguments.

```
leftOrRight : [ln rn of Nat] := ln 42
```

We can eliminate terms of extensible sum types using ordinary pattern matching.

```
extensible-abort : [ina of A, inb of B, ine of Empty] -> [ina of A, inb of B]
| ina a => ina a
| inb b => inb b
| ine e => abort e
```

Above, we have two boring clauses `ina a => ina a` and `inb b => inb b`. This kind of thing will happen quite often in functions between extensible sum types, so we have a special syntax for it: we don't need to write these identity clauses and we only need to handle the non-identity cases.

```
extensible-abort : [ina of A, inb of B, ine of Empty] -> [ina of A, inb of B]
| ine e => abort e
```

One last thing to mention are uniqueness principles. In general extensible sums don't have uniqueness principles, but there is an exception: extensible sums with zero or one constructor do have an uniqueness principle.

In case of the empty extensible sum, written `[]`, this uniqueness principle just says that any two elements of `[]` are equal.

```
uniqueness-[] (x y : []) : x = y := refl
```

By the way, this shouldn't surprise us, as we may think of `[]` as being the same type as `Empty`, which is a strict proposition.

```
Empty-[] : Empty = [] := refl
```

For single-constructor extensible sums, the uniqueness principle should look more familiar: it just says that every value `x` of the type is equal to the constructor applied to the argument from which `x` was made. Note that we can use the dot syntax to access the argument of `x`'s constructor, just like in ordinary pattern matching.

```
uniqueness-single (x : [ctor (a : A)]) : x = ctor x.a := refl
```

Not papers:
- [Polymorphic Variants in the OCaml manual](https://ocaml.org/manual/polyvariant.html)
- [Polymorphic Variants in Real World OCaml](https://dev.realworldocaml.org/variants.html#scrollNav-4)

Papers:
- [Abstracting Extensible Data Types: Or, Rows by Any Other Name](https://www.pure.ed.ac.uk/ws/portalfiles/portal/87175778/Abstracting_extensible_data_types_MORRIS_DoA_tbc_VoR_CC_BY.pdf)
- [Programming with Polymorphic Variants](https://caml.inria.fr/pub/papers/garrigue-polymorphic_variants-ml98.pdf)

Less relevant papers:
- [Extensible Algebraic Datatypes with Defaults](http://zenger.org/papers/icfp01.pdf)
- [Extensible Programming with First-Class Cases](https://people.cs.uchicago.edu/~blume/papers/icfp06.pdf)

**Status: OCaml has polymorphic variants, but I'm not sure how close they are to what was presented above. In general, extensible sums are very rare and the above is mostly speculation.**

TODO:
- Write more about extensible sums.
- Make sure the `[]` notation for an empty extensible sum doesn't clash with the notation for the empty list. Also make sure it doesn't clash with the `[]()` notation used in the Markdown-like link syntax used in doc comments.
- Are there recursive extensible sums or do we need inductive types for this purpose?
- This section reads as if it were placed after the section on basic inductive types. Change this! (Or not...)
- If extensible sums are not possible, then the are subsumed by inductive types.
- In theory, getting records right should be enough to get sums right, as they are dual to records.

## [Inductive Types](Induction/) <a id="inductive-types"></a> [↩](#toc)

The syntax of inductive type definitions is most similar to that of Agda, but even more convenient. We also reduce the amount of bookkeeping and boilerplate by allowing the same constructor names in multiple types and by giving each inductive type its own namespace. All the usual restrictions apply, i.e. only strictly positive types are allowed.

The syntax for defining functions by pattern matching is most similar to that of Lean, but the semantics of pattern matching are more unusual. All clauses in a definition by pattern matching constitute computational equalities, the clauses may be overlapping provided that the right-hand sides are equal when the clauses do overlap, and execution is independent of the order in which the clauses are given. As usual, all functions must be terminating and pattern matching has to cover all possible cases. We also have some convenient syntax sugar that allows non-linear pattern matching for types with decidable equality. But in case you need the more usual and mundane kind of pattern matching known from Coq or Agda, you can use it too!

Our inductive types are quite powerful. Besides basic inductive types, which can have parameters or be defined mutually with other inductive types, we have special support for Nested Inductive Types (the termination checker can recognize higher-order recursive calls). We also support Computational Inductive Types, in which constructors can perform some computations, Higher Inductive Types, in which constructors can create new paths in the type, and Nominal Inductive Types, which can represent abstract syntax trees of logics, calculi and programming languages.

We also support Inductive Families, including Nested Inductive Families (in which the inductive occurrences in the indices are nested in some type constructor), inductive-inductive types (in which we mutually define an inductive type and an inductive family indexed by this type) and inductive-recursive types (in which we mutually define an inductive type and a recursive function whose domain is this type).

### Basic Inductive Types <a id="basic-inductive-types"></a> [↩](#toc)

Basic inductive types work mostly as usual, but as for functions, we want to think that all constructors take just one argument which is a (possibly dependent) record.

The different genres of inductive types (enumerations, parameterized types, inductive families, etc.) have progressively more complete syntaxes, so that simple types can be written in a simple way and only the more complicated ones require more details.

Enumerations can NOT be written in a single line and must have the initial bar. Note that we don't need to (and should not) write the codomain of the constructors when it's the same in every case.

```
data Bool : Type
| ff
| tt
```

Definitions by pattern matching are very concise.

```
notb : Bool -> Bool
| ff => tt
| tt => ff
```

We should name the argument of each constructor, as this will be used for automatic name generation - something well known to be lacking in most proof assistants.

```
data _*_ (A B : Type) : Type
| pair of (outl : A, outr : B)
```

This doesn't affect the ordinary way of doing pattern matching that binds names.

```
swap : A * B -> B * A
| pair x y => pair y x
```

But if we want, we can name the function's argument and then rely on its constructor arguments' original names in definitions by pattern matching.

```
swap : (x : A * B) -> B * A
| pair => pair x.outr x.outl
```

Things are even more comfortable: because records get opened/unpacked automatically, we don't need to name the function argument, as we may simply use the name `outl` and `outr` (but we won't use this feature too much in the following sections).

```
swap : A * B -> B * A
| pair => pair outr outl
```

If there are name conflicts, we need to disambiguate by naming the arguments.

```
putTogether : (x y : A * B) -> A * B
| pair, pair => pair x.outl y.outr
```

As usual, the inductive type being defined can appear as argument to any of the constructors, provided that it stands in a strictly positive position.

```
data Nat : Type
| z
| s of (pred : Nat)
```

More complicated nested patterns that don't follow the type's structure are perfectly fine.

```
half : Nat -> Nat
| z       => z
| s z     => z
| s (s n) => s (half n)
```

We can use `@` to name a subpattern.
```
fib : Nat -> Nat
| z           => z
| s z         => s z
| s n1@(s n2) => fib n1 + fib n2
```

We make a distinction between **parameters**, which are bound to the left of the main colon, and **indices**, which are bound to the right of the main colon. The difference is that parameters always stay the same, so that we don't need to write them explicitly. Indices can change, so we must write them explicitly.

In the definition of the type of `List`s below, this manifests in that we write `tl : List` for the tail of the list instead of `tl : List A` as we would if `A` were an index. Also note that we allow constructor names to be symbols, including infix symbols, just like in Agda.

```
data List (A : Type) : Type
| []
| _::_ of (hd : A, tl : List)
```

This distinction applies both to inductive and recursive definitions. It looks a bit weird at first, as that's not what people are used to, but hey, you are going to appreciate it when the definitions get more complicated!

```
map (f : A -> B) : List A -> List B
| []     => []
| h :: t => f h :: map t
```

The distinction between parameters and indices has some other consequences too. For example, when defining additions of naturals, the most succinct definition forces us to do it by recursion on the second argument.

```
add (n : Nat) : Nat -> Nat
| z   => n
| s m => s (add m)
```

For functions that are not commutative, like list append, we get a bit more headache, as we need to match two arguments even though we don't use the second one.

```
app : (l1 l2 : List A) -> List A
| []    , _ => l2
| h :: t, _ => h :: app t l2
```

In case we need to match something else besides the arguments, we can use a `with`-clause.
```
filter (p : A -> Bool) : List A -> List A
| [] => []
| h :: t with p h
  | tt => h :: filter t
  | ff => filter t
```

The above use of a `with`-clause is equivalent to the following use of an `if-then-else` expression.

```
filter (p : A -> Bool) : List A -> List A
| []     => []
| h :: t => if p h then h :: filter t else filter t
```

Papers:
- [Inductive Types Deconstructed](https://www.iro.umontreal.ca/~monnier/itd-tyde-2019.pdf)
- [Elaborating Inductive Definitions](https://arxiv.org/pdf/1210.6390.pdf)
- [The Gentle Art of Levitation](https://www.irif.fr/~dagand/papers/levitation.pdf)
- [A Cosmology of Datatypes](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.366.3635&rep=rep1&type=pdf)
- [The view from the left](http://strictlypositive.org/vfl.pdf.)

**Status: inductive types, pattern matching and structural recursion are standard, with Agda probably being the closest implementation to what has been described so far.**

TODO:
- Make sure that `@` used for as-patterns doesn't clash with `@` used for explicit arguments and `@` used for name concretion.
- Come up with some syntax for explicit arguments in function applications!

### Various syntactic conveniences for inductive types <a id="syntactic-conveniences-for-inductives"></a> [↩](#toc)

In this section we list various tiny convenience features and syntax sugars that we may use when working with inductive types.

#### Constructor names may overlap between types <a id="non-unique-constructor-names"></a> [↩](#toc)

Names of inductive type constructors do NOT need to be globally unique, unlike in many other languages - multiple types can have constructors with the same names.

```
data TrafficLight : Type
| Red
| Orange
| Green

data Color : Type
| Red
| Green
| Blue
| RGBA of (r g b a : u8)
```

Both of the above types have constructors named `Red` and `Green`, but there is no confusion between them. For example, if we apply a function `canDrive : TrafficLight -> Bool` to `Red`, i.e. `canDrive Red`, then `Red` is interpreted as `Red : TrafficLight`. If a color is expected, e.g. in `isPretty Red` for `isPretty : Color -> Bool`, `Red` is interpreted as `Red : Color`. If we need to disambiguate between the two `Red`s, we can write `TrafficLight.Red` and `Color.Red`, respectively.

**Status: supporting name clashes is a rather rare feature. It is somewhat supported in Coq, but works very badly and is very confusing. It was supported in Idris 1 and worked pretty well there. Overall, I guess it could be tricky, but in the end it's just a matter of getting it right.**

#### The namespace associated with an inductive type <a id="associated-namespace"></a> [↩](#toc)

Above, the `TrafficLight` in `TrafficLight.Red` and the `Color` in `Color.Red` are not the type (names) themselves, but the namespaces associated with these types - in our language, every inductive type has a namespace associated with it.

The namespace is named the same as the type. We may access the contents of this namespace with dot syntax, just like for records. In fact, the namespace associated to an inductive type is nothing more than a record that holds various useful things related to the type.

```
> :t List.Nil
List.Nil : (#A : Type) -> List A

> :t List.Cons
List.Cons : (#A : Type, hd : A, tl : List A) -> List A
```

As we have already seen, the namespace of an inductive type contains its constructors.

```
> :def List.Nil.args
List.Nil.args : Type := (A : Type) -> ()

> :def List.Cons.args
List.Cons.args : Type := (A : Type) -> (hd : A, tl : List A)
```

Besides the constructors themselves, the namespace also contains types that represent the constructors' arguments (parameterized by the type's parameters).

```
> :def List.params
List.params : Type := (A : Type)
```

Speaking of parameters, `I.params` is the type that collects all parameters of the inductive type `I`. For `List`, there is only one parameter, namely the type `A`, so `List.params` is a record with one field, `A : Type`.

```
> :t List.elim
List.elim : (#A : Type, P : A -> Type, nil : P Nil, cons : (hd : A, tl : List A, IHtl : P tl) -> P (Cons hd tl), l : List A) -> P l
```

Another thing that we may find in this namespace is the type's elimination principle. The elimination principle of type `I` is called `I.elim`. For example, the induction principle for `List` is called `List.elim`.

```
> :def List.Extras.Base
data List.Extras.Base A (A X : Type) : Type
| NilX
| ConsX of (hd : A, tl : X)
```

The namespace contains even more than what was listed above, including the base functor of the type, it's parametricity translation (for `List`, that would be `Forall` and `Forall`), a characterization of the type's equality (if it's trivial enough to automatically generate), a decision procedure for equality, and so on. All of these extras may be found in the subnamespace `List.Extras`.

Not papers:
- [How inductive type namespacing works in Lean](https://leanprover.github.io/theorem_proving_in_lean/inductive_types.html#enumerated-types)

**Status: each inductive type being its own namespace/module is not standard, but implemented in Lean, so if we have namespaces, then autogenerating one for each inductive type should be easy enough. The parameters, constructor arguments and so on already have their representations at the AST level, so turning them into proper types and putting in these namespaces should be easy. Generating the more complicated stuff like decision procedures for equality would be harder.**

#### Discriminators and the `is` syntax for single-case pattern matching <a id="discriminators-and-single-case-pattern-matching"></a> [↩](#toc)

A **discriminator** is a function which checks whether a term of an inductive type was made with a particular constructor. This idea is taken from the F* language. Here, discriminators are named after the constructor, with a `?` at the end, and autogenerated when the type is defined. They come handy particularly in preconditions.

In our language we also want to have discriminators, but we don't need to write them by hand. The solution is to introduce a new syntactic construct for doing single-case pattern matching: `is`. The expression `t is p` matches the term `t` against the pattern `p` and returns a boolean (`tt` if the match was successful, `ff` otherwise).

```
> :eval 42 is s
tt : Bool
```

Using `is`, the discriminators for `Nat` can be defined as

```
z? (n : Nat) : Bool := n is z

s? (n : Nat) : Bool := n is s
```

We can combine this new syntax with the usual boolean `if _ then _ else`: if the pattern was matched and any variables were bound, they become available in the `then` branch of the `if`. This way we can use `is` to define much more than just discriminators. Of course we can nest these `if`-`is`-`then`-`else` expressions, but it's smarter to use ordinary pattern matching in such cases. In the examples below, we show how to use `is` to define the `pred`ecessor function for naturals and `add`ition as a one-liner.

```
pred : (n : Nat) -> Option Nat :=
  fun n => if n is s n' then Some n' else None

add : (n m : Nat) -> Nat :=
  fun n m => if n is s n' then s (add n' m) else m
```

The `is` syntax of course also works when we want to access constructor arguments by name.

```
add (n m : Nat) : Nat :=
  if n is s then s (add n.pred m) else m
```

Besides `if _ then _ else`, we can also use `is` at the type level, as the premise of an implication or a field of a record. In such a case, the boolean result of `is` is casted to a proposition - `tt` becomes `Unit`, whereas `ff` becomes `Empty`. This comes handy, as it allows us to access constructor arguments by name in the implication's conclusion or in later fields of the record. In the snippet below, we show how to define a relation saying that two lists have the same head, using premises with `is` instead of pattern matching, and a type of non-empty lists which uses a proof of `l is Cons` as a constructor argument.

```
listsWithTheSameHead (#A : Type) (l1 l2 : List A) : Type :=
  l1 is Cons -> l2 is Cons -> l1.hd = l2.hd

data NonEmptyList (A : Type) : Type :=
| Nel of (l : List A, nonempty : l is Cons)
```

Not papers:
- [Discriminators in F* tutorial](https://fstar-lang.org/tutorial/tutorial.html#sec-discriminators)
- [An example of the `is` syntax in SSReflect](https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html#congruence)

**Status: SSReflect has a syntactic construct called `is` that is somewhat similar to what was described above, so at the syntactic level implement `is` should be very easy. Making `is` first class (i.e. making `x is C` into a boolean or a type) would be a bit harder, but since it's supposed to just represent the result of a pattern match, it should be doable. Discriminators are not standard, but implemented in F\*, and once we have `is` they should pose no problems.**

TODO:
- How to represent `t is p` as a type? Take a look at papers about type theory with computational assumptions.
- How to unify the `is` syntax with ordinary pattern matching syntax?
- How to make patterns (and pattern matching) first-class?

#### Copattern syntax for constructor arguments <a id="copattern-syntax-for-constructor-arguments"></a> [↩](#toc)

When an inductive type's constructor has a lot of arguments, or argument names are very long, it becomes necessary to figure out how to best split the whole thing into multiple lines. To make this easier, we allow using the copattern syntax, which we have seen when dealing with records, to specify inductive types' constructor arguments.

```
data _*_ (A B : Type) : Type
| pair of
  & outl of A
  & outr of B

data Nat : Type
| z
| s of
  & pred of Nat

data List (A : Type) : Type
| []
| _::_ of
  & hd of A
  & tl of List

data Color : Type
| Red
| Green
| Blue
| RGBA of
  & r g b a : u8
```

The above code shows how to define the type from the previous section using this syntax. For `List`, for example, the beginning of the definition is the same as before, but when writing the arguments of `_::_` (i.e. cons), we list them on separate lines starting with `&`, like when defining a record.

**Status: since copattern syntax is already available for defining records, I don't see any problems with allowing it to define constructor arguments. Implementing it should probably be very easy.**

#### Single-argument constructors <a id="single-argument-constructors"></a> [↩](#toc)

Another convenient feature is that if an inductive type's constructor takes only a single argument, we don't need to wrap this argument into a record nor name it. We can just write `C of T`, where `C` is the constructor name and `T` is the argument type, and it will desugar to `C of (C : T)`, i.e. a record with single field whose name is the same as that of the constructor.

```
data Sum (A B : Type) : Type
| inl of A
| inr of B

data Sum' (A B : Type) : Type
| inl of (inl : A)
| inr of (inr : B)
```

As an example, the code above shows how to use this syntax sugar to define `Sum`. `Sum'` is the desugaring of `Sum`.

**Status: this is a very simple piece of syntax sugar, which should be easy to implement. The only complication occurs when the single argument is a record, but let's say that we can treat differently records defined inline (constructor arguments) and records defined somewhere else.**

#### Unnamed constructor arguments <a id="unnamed-constructor-arguments"></a> [↩](#toc)

Another convenient feature at our disposal is that we don't need to name constructor arguments that are proofs of very trivial propositions that can be decided during typechecking/elaboration. The most obvious of these is `Unit`, but we probably won't often need to have a field of this type. Another is `is`, the syntax we can use for abridged single-case pattern matching.

```
data PositiveNat : Type
| Mk of
  & n of Nat
  & n is s

data PositiveNat' : Type
| Mk of (n : Nat, n is s)
```

In the snippet above, we have defined the type of positive natural numbers `PositiveNat`. It has one constructor with an argument `n`, which is a `Nat`, and another argument, left unnamed, which is a proof of `n is s`, i.e. that `n` is not zero. `PositiveNat'` is a version of the same type, but defined using tuple syntax instead of copattern syntax.

**Status: Coq allows naming record fields `_`, but I'm not sure about Agda, Lean or Idris. In any case, I think supporting this at the syntactic level should be easy. Inferring the proofs of `is` should also be fairly trivial.**

TODO:
- Write a section on unnamed record fields.
- Figure out a precise set of propositions for which this is allowed.

#### Syntax sugar for bundled parameters <a id="bundled-parameters"></a> [↩](#toc)

As was already said, we distinguish between parameters and indices in function definitions, the consequence being that we can omit the parameters, but we must write the indices. Similarly, we can omit parameters in inductive type definitions.

This is nice, but not enough to guard us from repetitiveness and boredom, as we still need to spell out all the parameters in the function's declaration and then pass them to the type. Even though the former can be dodged by using the mechanism of very implicit arguments (as we often do), so far there's nothing we can do about the latter. Until now!

```
len : List -> Nat
| []     => z
| _ :: t => s (len t)
```

The above snippet defines `len`, the function that computes the length of a list. Note that its type is given as `List -> Nat`. Taken at face value this is not a well-formed type, because `List : Type -> Type` is a type constructor, not a type. However, `List -> Nat` is just syntax sugar which should be interpreted as `(#A : Type) -> List A -> Nat`, as shown below.

```
// With very implicit arguments.
len : List A -> Nat
| []     => z
| _ :: t => s (len t)

// With ordinary implicit arguments.
len (#A : Type) : List A -> Nat
| []     => z
| _ :: t => s (len t)
```

In general, whenever a type constructor (like `List : Type -> Type` or `_ * _ : Type -> Type -> Type`) is used where a type is expected, we should interpret this as referring to the type's constructor _record closure_ (i.e. `(A : Type, _ : List A)` or `(A B : Type, _ : A * B)`). This syntax sugar is called **bundled parameters**.

```
app : (l1 l2 : List) -> List
| []    , _ => l2
| h :: t, _ => h :: app t l2
```

The above piece fo code defines the `app` function once more, this time using bundled parameters.

In general, separate uses of `List` will be understood to mean `List` with different element types, unless it is inferred that the element types should be the same.

For example, the type `(x : List, y : List)` should be interpreted as `(A : Type, x : List A, B : Type, y : List B)`. However, if we put `x` and `y` together in the same binder, as in `(x y : List)`, then it is understood that `x` and `y` are of the same type, so this type should be inrepreted as `(A : Type, x y : List A)`.

In our `app` example above, both `l1` and `l2` appear in the same binder, so it is inferred that they must be of the same type, i.e. the binder is interpreted as `(#A : Type, l1 l2 : List A)`. But what about the codomain, which is also written as `List`? Is it interpreted as `(#B : Type, List B)` or as `List A`? The answer is that the codomain is always interpreted using parameters introduced in the domain, so it is interpreted as `List A`.

```
app (#A : Type) : (l1 l2 : List A) -> List A
| []    , _ => l2
| h :: t, _ => h :: app t l2
```

To sum up, the type of `app`, written as `(l1 l2 : List) -> List` is interpreted as `(#A : Type, l1 l2 : List A) -> List A`, and the definition of `app` is equivalent to the definition shown above.

Papers:
- None, this is my idea.

**Status: the distinction between parameters and indices was present in Lean 2 when defining functions, but its other forms described here are novel. In Coq, the syntax is similar to ours when the parameters of an inductive type are abstracted over inside a section. To sum up, it shouldn't pose any implementation problems.**

TODO:
- Describe bundled syntax for inductive families. Review section on bundled syntax for ordinary inductive types.

### [Overlapping and Order-Independent Patterns](Induction/OverlappingPatterns) <a id="overlapping-patterns"></a> [↩](#toc)

Consider a different definition of addition of natural numbers, one that matches both of its arguments.

```
add : (n m : Nat) -> Nat
| z   , m => m
| s n', m => s (add n' m)
```

It's all right and good, but even though `add n z` equals `n`, it does not compute to `n`. Similarly, even though `add n (s m')` equals `s (add n m')`, it doesn't compute to `s (add n m')`. Overlapping patterns are a way to make this happen.

```
add : (n m : Nat) -> Nat
| z   , m    => m
| s n', m    => s (add n' m)
| n   , z    => n
| n   , s m' => s (add n m')
```

Here besides the two clauses from the previous definitions, we have two more clauses which amount to saying that "additionally, `add n z` computes to `z` and `add n (s m')` computes to `s (add n m')`".

For the definition to be accepted, all the clauses need to be confluent, i.e. they must return the same result when they overlap. In our example, the overlapping cases are `add z z` and `add (s n') (s m')`. But `add z z` computes to `z` both using clause 1 and 3, so it's ok. Similarly, `add (s n') (s m')` computes to `s (s (add n' m'))` using first clause 2 and then clause 4, and it computes to the same result using first clause 4 and then clause 2, so it's ok.

These new computational equalities greatly reduce the number of rewrites needed in proofs, but it also and makes dependently-typed programming much easier in some cases. For example, for vectors the terms `v ++ []` used to have the problematic type `Vec A (add n z)`, whereas now it has the less problematic type `Vec A n`. Yay!

Of course, there are some problems with this new kind of pattern matching. The foremost of them is that the catch-all pattern `_` starts being problematic. Consider the decision function for equality of naturals:

```
%Fail
dec : (n m : Nat) -> Bool
| z   , z    => tt
| s n', s m' => dec n' m'
| _   , _    => ff
```

This definition is illegal, because `dec z z` computes to `tt` according to the first clause, but it computes to `ff` according to the third clause.

To remedy this, we have to keep the old semantics of pattern matching (which we call _first-match semantics_). So from now on we have two kinds of pattern matching: the usual one with first-match semantics and the new one, in which patterns can be _overlapping_ and whose semantics don't depend on the _order_ in which the patterns appear in code. We can use the pragmas `%FirstMatch` and `%OverlappingPatterns` to specify, which kind of pattern matching we use.

```
%FirstMatch
dec : (n m : Nat) -> Bool
| z   , z    => tt
| s n', s m' => dec n' m'
| _   , _    => ff
```

Now the definition is ok, because we explicitly mark the fact that it uses the first-match semantics.

Note that allowing overlapping patterns has some deep metatheoretical consequences, namely that definitions by pattern matching can no longer be translated into definitions with eliminators. However, we consider this price to be worth paying.

Papers:
- [Overlapping and Order-Independent Patterns: Definitional Equality for All](https://link.springer.com/content/pdf/10.1007%2F978-3-642-54833-8_6.pdf)

**Status: prototype implemented in Agda 2.6.1.**

TODO:
- Invent a blend of first-match patterns and overlapping patterns which subsumes both of them.

### Decidable Equality Patterns <a id="decidable-equality-patterns"></a> [↩](#toc)

For types which have decidable equality, while pattern matching we can use non-linear patterns and get them desugared into uses of the corresponding decision procedure for equality.

```
dedupConsecutive (#A : EqType) : List A -> List A
| []          => []
| h :: h :: t => dedupConsecutive (h :: t)
| h :: t      => h :: dedupConsecutive t
```

For example, we can use this feature to implement the above function which removes adjacent duplicates from a list, provided that the type of elements has decidable equality. This will be automatically desugared to the definition below.

```
dedupConsecutive (#A : EqType) : List A -> List A
| [] => []
| x :: y :: t with x =? y
  | tt =>      dedupConsecutive (y :: t)
  | ff => x :: dedupConsecutive (y :: t)
```

Note that the semantics of the non-linear matches are the classical first-match semantics and it looks like it'd be hard to transplant this into the setting of overlapping and order-independent patterns. 

Not papers:
- [mailing list with discussion on why non-linear patterns are not allowed in Haskell](https://www.mail-archive.com/haskell@haskell.org/msg03721.html)

**Status: no papers and nowhere implemented, but looks very easy to get right.**

### A more flexible syntax for pattern matching <a id="flexible-pattern-matching"></a> [↩](#toc)

So far we have seen the usual syntax and semantics for pattern matching, i.e. patterns written positionally that then get interpreted using the first-match semantics. We have also seen an alternative syntax for pattern matching in which we don't need to name pattern variables, but instead we refer to constructor arguments with dot syntax, and an alternative semantics, which we call Overlapping and Order-Independent Patterns.

Now it's time to see an extended version of the alternative syntax, which we call _Flexible Patterns_. The idea is an extension of what we have already seen - we can omit pattern arguments and only write the constructor names. In this section, we will compare Flexible Patterns with the traditional syntax on a case by case basis.

```
%StandardPatterns
map (f : A -> B) : List A -> List B
| Nil => Nil
| Cons h t => Cons (f h) (map t)

%FlexiblePatterns
map (f : A -> B) : (l : List A) -> List B
| Nil  => Nil
| Cons => Cons (f l.hd) (map l.tl)
```

Let's start with the very basics. The first definition of `map` uses standard pattern matching. In the second patern, we write `Cons h t`, so that on the right-hand side we can refer to the list's head as `h` and to its tail as `t`.

The second definition of `map` uses Flexible Patterns. In the second pattern we write just `Cons`, without binding its arguments, and then on the right-hand side we refer to the head and tail of the list as `l.hd` and `l.tl`, respectively, where `l` is the name of the list.

Note that we have two directives that we can optionally use to mark the particular pattern matching syntax we use - `%FlexiblePatterns` refers to the new syntax, whereas `%StandardPatterns` refers to the old syntax. However, in the rest of the section we won't use these directives, and instead we follow the convention that the first definition uses the standard syntax, whereas the second uses Flexible Patterns.

```
last : List A -> Option A
| Nil => None
| Cons h Nil => Some h
| Cons _ t => last t

last : (l : List A) -> Option A
| Nil  => None
| Cons (tl is Nil) => Some l.hd
| Cons => last l.tl
```

In the above example, we define the function `last` using nested patterns. Note that in both cases, we use the first-match semantics.

Using the standard syntax, we write `Cons h Nil` to match the singletion list `[h]` and `Cons _ t` to match a non-singleton list and name it's tail `t`.

Using Flexible Patterns, we match the singleton list `[h]` using the pattern `Cons (tl is Nil)`, and the non-singleton list simply using `Cons`.

```
%OverlappingPatterns
last : List A -> Option A
| Nil => None
| Cons h Nil => Some h
| Cons _ t@(Cons _ _) => last t

%OverlappingPatterns
last : (l : List A) -> Option A
| Nil  => None
| Cons (tl is Nil) => Some l.hd
| Cons (tl is Cons) => last l.tl
```

If we wanted to use `%OverlappingPatterns`, the patterns become a bit more complicated. The standard pattern for `[h]` is still `Cons h Nil`, but to match a non-singleton list we need to write `Cons _ @t(Cons _ _)`, with the as-pattern `t@` used to refer to the whole `Cons _ _` on the right-hand side.

Using Flexible Patterns, things look much more uniform: to match a singleton list, we write `Cons (tl is Nil)` and to match a non-singleton list, we write `Cons (tl is Cons)`.

```
last : (l : List A) -> Option A
| Nil  => None
| Cons with l.tl
  | Nil  => Some l.hd
  | Cons => last l.tl

last : (l : List A) -> Option A
| Nil  => None
| Cons => if l.tl is Nil then Some l.hd else last l.tl
```

Note that neither the standard nor the flexible syntax from the previous example seems to be the best way of defining the function `last`. Instead, it seems that the most elegant way is to use a `with`-clause, like in the snippet above. Also note that using the `is` syntax turns out to also be quite an elegant choice for `last`.

```
third : (l : List A) -> Option A
| Cons _ (Cons _ (Cons _ (Cons x _))) => Some x
| _ => None

third : (l : List A) -> Option A
| Cons (tl is Cons (tl is Cons (tl is Cons))) => Some l.tl.tl.tl.hd
| _ => None
```

In general, nested standard patterns have the form `C ... (C' ... (C'' ...))`, whereas nested flexible patterns have the form `C (arg is C' (arg' is C'' (...)))`.

This is shown in the snippet above where we define the function `third`, which retrieves the third element from a list. With standard patterns, we just need to put 4 `Cons`s together (we start indexing at zero), whereas with flexible patterns we have a similar, but a bit longer and more annoying chains of `Cons (tl is Cons (...))`.

```
%FlexiblePatterns
third : (l : List A) -> Option A
| l.tl.tl.tl is Cons => Some l.tl.tl.tl.hd
| _ => None

%FlexiblePatterns
third : (l : List A) -> Option A
| tl.tl.tl is Cons => Some l.tl.tl.tl.hd
| _ => None
```

To save ourselves from typing `(Cons (tl is ...))`, we allow to write this pattern differently: we can use the dot syntax on the left-hand side of the pattern, like `l.tl.tl.tl`, and then use an `is`-clause to specify what this chain of field accessors should match. This way, `l.tl.tl.tl is Cons` is a pattern that says "the tail of the tail of the tail of `l` is made with the `Cons` constructor". To be even more concise, we also allow dropping the initial `l`, since we know that `tl` must refer to `l.tl` (if we had two lists, we would need to write their names explicitly for disambiguation, though).

```
data Color
& r g b a of u8

f : (l : List (List Color)) -> Option u8
| l.tl.hd.tl is Cons => Some l.tl.hd.tl.hd.a
```

Of course, we can use this chained-dot-patterns also for non-recursive constructor arguments - i.e. we can use them to match nested records. In the above example, we show how to get the alpha channel from the `Color` with coordinate `(1, 1)` in a two-dimensional `List` of `List`s.

```
data BT (A : Type) : Type
| E
| N of (v : A, l r : BT)

weird-test : (t : BT A) -> Type
| t.l.l.l.(l is N, r is N) => t.l.l.l.l.v = t.l.l.l.r.v
```

Another nice convenience feature when using these chained-dot-patterns is that we can avoid repeating prefixes when we want to match two or more deeply nested values. In the example above, we want to compare the values that are four times to the left of the root and three times to the left and once to the right. We can do this with the pattern `t.l.l.l.(l is N, r is N)`, which should be interpreted as a conjunction of `t.l.l.l.l is N` and `t.l.l.l.r is N`. These kinds of _branching patterns_ can also be nested themselves.

```
@FlexiblePatterns
f : (l : List (List Color)) -> Option u8
| x@(l.tl.hd.tl) is Cons => Some x.hd.a

@FlexiblePatterns
weird-test : (t : BT A) -> Type
| x@(t.l.l.l).(l is N, r is N) => x.l.v = x.r.v
```

Chained-dot-patterns are really nice, but they can get a bit heavy syntactically. In the snippet above we define the functions `f`and `weird-test` once more, but this time we combine the chained-dot-patterns with as-patterns, using the `name@pattern` syntax, to avoid having to repeat a long chain of accessors.

```
zipWith (f : A -> B -> C) : (la : List A, lb : List B) -> List C
| Nil, _ => Nil
| _, Nil => Nil
| Cons a ta, Cons b tb => Cons (f a b) (zipWith ta tb)

zipWith (f : A -> B -> C) : (la : List A, lb : List B) -> List C
| la is Nil => Nil
| lb is Nil => Nil
| Cons, Cons => Cons (f la.hd lb.hd) (zipWith la.tl lb.tl)
```

The next feature of flexible patterns is that they avoid writing too many underscores. In the snippet above, we define the function `zipWith` on `List`s. There are two `Nil` cases and using standard syntax we need to write them both in full as `Nil, _` and `_, Nil`, respectively, whereas using flexible patterns we can simply write `la is Nil` and `lb is Nil`, respectively, without mentioning any patterns for the list that we don't care about.


Papers:
- None, this is my own idea.

**Status: Flexible Patterns are very speculative, as the idea is mine. However, I think it would be moderately easy to implement them.**

TODO:
- Search for papers.
- Rethink the two syntaxes of pattern matching.
- Try to find other possible pattern matching syntaxes.
- Find other semantics for pattern matching.
- How does this dualize to copattern matching?
- Find out how to combine standard pattern matching with Overlapping and Order-Independent Patterns.

### Mutual Inductive Types <a id="mutual-inductive-types"></a> [↩](#toc)

Ordinary inductive types can refer to themselves in the constructors' arguments. Mutual Inductive Types generalize this setting - now inductives in the constructors' arguments can refer to other inductive types that in turn refer to them.

```
data List' (A : Type) : Type
| Empty
| NonEmpty of (ne : NonEmptyList)

and

data NonEmptyList (A : Type) : Type
| Cons of (hd : A, tl : List')
```

The above code defines by mutual induction two types - the first represents lists, the other non-empty lists (components of a mutual definition are separated by the `and `keyword). Values of type `List'` are either `Empty` or they are a `NonEmptyList` wrapped in the constructor `NonEmpty`, whereas `NonEmptyList`s are just a head and a tail (which is a `List'`), wrapped in the constructor `Cons`.

Note that our convention regarding parameters is upheld - we don't need to write the type parameter `A`, neither when referring to `List'` in the `Cons` constructor, nor when referring to `NonEmptyList` in the `NonEmpty` constructor. However, this is the case only because both types have the same parameters - as soon as they differ, we need to explicitly write them in all occurrences of a given type, except in its own definition.

```
mapl (f : A -> B) : List' A -> List' B
| Empty       => Empty
| NonEmpty ne => mapne ne

and

mapne (f : A -> B) : NonEmptyList A -> NonEmptyList B
| Cons h t => Cons (f h) (mapl t)
```

Functions out of mutual inductive types can be defined by mutual recursion. Above, we define the two counterparts of usual `List`'s `map`. The function `mapl`, which maps `f` over a `List'`, refers in its `NonEmpty` case to `mapne`, which maps `f` over a `NonEmptyList`.

Note that our convention regarding parameters is also upheld here - we don't need to mention the function `f` when applying either `mapl` or `mapne`. Just as for mutual type definitions, this is the case only when all of the mutual definitions have the same parameters - in case they don't, we need to explicitly provide them in all recursive calls, except when a function calls itself directly. Also note that we could have called both `mapl` and `mapne` just `map`, but we didn't do that to make the example less confusing. Just as for types, both definitions are separated by the `and` keyword.

```
even : Nat -> Bool
| z    => tt
| s n' => odd n'

and

odd : Nat -> Bool
| z    => ff
| s n' => even n'
```

Mutual recursion is not restricted to mutual inductive types only. Above we have an example of functions for checking whether a `Nat`ural number is `even` or `odd` defined by mutual recursion, even though the domain of both of them is `Nat`.

```
mutual
  (A : Type)

  data List' : Type
  | Empty
  | NonEmpty of (ne : NonEmptyList)

  data NonEmptyList : Type
  | Cons of (hd : A, tl : List')

mutual
  #(A B : Type) (f : A -> B)

  mapl : List' A -> List' B
  | Empty       => Empty
  | NonEmpty ne => mapne ne

  mapne : NonEmptyList A -> NonEmptyList B
  | Cons h t => Cons (f h) (mapl t)
```

Last but not least, besides the standard `and` syntax that we have seen, there's also an alternative syntax for defining mutual inductive types and mutual recursive functions. We can define them in blocks which start with the keyword `mutual`. Then, we may list parameters shared by all definitions. Finally, we may give the definitions proper, _without_ using the `and` keyword.

Above we show how to use this syntax to once more define `List'`, `NonEmptyList`, `mapl`, and `mapne`. It may not seem very useful, because the new definitions are longer than the original ones, but the `mutual` block style definitions should prove useful when there are many definitions that share many parameters - in such cases we save quite a lot of writing.

```
mutual
  ...
end

mutual NamedMutualBlock
  ...
end

mutual NamedMutualBlock'
  ...
end NamedMutualBlock'
```

As a slight readability bonus, we may optionally end `mutual` definitions with the `end` keyword. We may also optionally name the `mutual` block - this provides even more readability. If a named `mutual` block is ended with the `end` keyword, we may also repeat its name after the `end` keyword, for even more readability.

Not papers:
- [Syntax of mutual blocks in Agda](https://agda.readthedocs.io/en/latest/language/mutual-recursion.html#mutual-recursion-mutual-block)
- [Syntax of new mutual blocks in Agda](https://agda.readthedocs.io/en/latest/language/mutual-recursion.html#mutual-recursion-interleaved-mutual)

**Status: mutual inductive types and mutual recursion are standard in proofs assistants and in functional programming. Regarding the `mutual` block syntax, Agda has it and it used to be the only way of defining mutual inductive types, but recently Agda made it obsolete. To sum up, there might be some syntactic problems, since Agda made this decision for a reason.**

TODO:
- What are the exact rules for termination checking of mutual recursion?

### Nested Inductive Types <a id="nested-inductive-types"></a> [↩](#toc)

Nested Inductive Types are inductive types `I` in which the inductive occurrences of `I` appear as an argument of some type family (besides the arrow `(->) : Type -> Type -> Type`, of course, as it's supported by ordinary inductive types). These types can be defined in our language as ordinary inductive types, but writing functions that operate on Nested Inductive Types requires some more explanation.

One of the most iconic examples of Nested Inductive Types is the type of rose trees, i.e. trees that have a `List` of subtrees.

```
data RoseTree (A : Type) : Type
| E
| N of (v : A, ts : List RoseTree)
```

Functions out of such types can be defined as usual by pattern matching and recursion, with the nested recursion (i.e. on the `List` in case of `RoseTree`) being handled just fine.

```
size : RoseTree A -> Nat
| E      => 0
| N _ ts => 1 + sum (map size ts)
```

In the above example, we compute the `size` of a `RoseTree`. To do this, we use auxiliary functions `map : (A -> B) -> List A -> List B` and `sum : List Nat -> Nat` (whose implementation is not shown). There are no explicit recursive calls - they are hidden in `map size`, i.e. they happen only inside `map`. This use of recursion, called _higher-order recursion_ (because unapplied/partially applied `size` is used as an argument to a higher-order function) is perfectly legal in our language.

There are a few other ways to implement `size`.

```
size : RoseTree A -> Nat
| E             => 0
| N _ []        => 1
| N v (t :: ts) => size t + size (N v ts)
```

In the variant above we use ordinary recursion. The interesting constructor, `N`, is split into two cases: if there are no subtrees, we return `1`, whereas if there are, we call `size` recursively on the first subtree `t` and then on `N v ts`, i.e. on what remains of our original `RoseTree` after we remove the first subtree `t`.

These recursive calls are perfectly legal - `t` is a subterm of `N v (t :: ts)`, so `size t` is a good recursive call. `N v ts` is not a subterm of `N v (t :: ts)`, but it is smaller in an obvious way, and the termination checker sees that.

```
size : RoseTree A -> Nat
| E => 0
| N v ts with ts
  | []       => 1
  | t :: ts' => size t + size (N v ts')
```

The variant above is very similar to the previous one, but we use a `with`-clause to split the `N` case into two. This might come handy when the inner type (the `List` in our `RoseTree` example) has a lot of constructors.

```
size : RoseTree A -> Nat
| E => 0
| N _ ts => 1 + List.rec 0 (fun t ts => size t + ts) ts
```

In the variant above we use recursion on the list of subtrees instead of on the `RoseTree` itself. We do this by using the recursor for lists `List.rec : (#A #R : Type, nil : R, cons : A -> R -> R, x : List A) -> R`. The only explicit recursive call, `size t`, occurs under the `fun`. This is also perfectly legal and the termination checker can see it.

```
size : RoseTree A -> Nat
| E      => 0
| N _ ts => 1 + size' ts

and

size' : List (RoseTree A) -> Nat
| []     => 0
| h :: t => size h + size' t
```

Yet another way to implement `size` (and one that is probably the most universal, in the sense of also working in other languages and proof assistants) is to use mutual recursion: to compute the `size` of a `RoseTree` we refer to the auxiliary function `size'`, which computes the size of a `List` of `RoseTree`s, and which in turn refers to `size`.

```
data RoseTree (A : Type) : Type
| E
| N of (v : A, ts : RoseTreeList)

and

data RoseTreeList (A : Type) : Type
| Nil
| Cons of (h : RoseTree, t : RoseTreeList)
```

Last but not least, the mutually recursive implementation of `size` and `size'` points to the commonly known fact that we can represent Nested Inductive Types using Mutual Inductive Types. In fact, this kind of translation is exactly one idea how to provide full support for Nested Inductive Types in practice.

Papers:
- [Generating Induction Principles for Nested Inductive Types in MetaCoq](https://www.ps.uni-saarland.de/~ullrich/bachelor/thesis.pdf)

Not papers:
- [Compiling nested inductive types in Lean](https://github.com/leanprover/lean/wiki/Compiling-nested-inductive-types)

**Status: Nested Inductive Types can be defined in any language that supports ordinary inductive types. Coq, Agda and Lean all have them. The only problem is providing good support for termination checking of functions out of such types.**

TODO:
- Write some example code.

### Negative Inductive Types <a id="negative-inductive-types"></a> [↩](#toc)

So far we have only seen _Positive_ Inductive Types. By positive, I mean that these types are like (extensible) sums, i.e. they can be made using one of possibly many different constructors, which then take a record of arguments.

In our language, we can have not only Positive Inductive Types, but also _Negative_ Inductive Types. By negative I mean that these types are like records, i.e. they can have many fields of different types, which we then need to provide to define a value of the type. But there's one thing that makes them different from records: we can have fields of the same type that is being defined, and in general the field types can mention the type being defined.

Let's see an example which will make everything clearer.

```
data NETree (A : Type) : Type
& root of A
& ts   of List NETree
```

The above snippet defines the type `NETree`, whose name is an abbreviation of "non-empty tree". Values of this type are trees that have a `root` and a `List` of subtrees, which are `NETree`s themselves.

The syntax of our definition is as follows. We start with the `data` keyword, which indicates that we are defining an inductive type. Then we provide the parameters (in our case `A : Type`) and the universe to which the defined type belongs (for us, `Type`). Then in each line, starting with the symbol `&`, we list fields that values of the type must have, just like for records.

```
data NETree (A : Type) : Type
constructor N
& root of A
& ts   of List NETree
```

Note that we can optionally provide a name for the type's only constructor. For `NETree`, we chose `N`, our standard name for `N`odes of trees.

```
t : NETree Nat
& root => 42
& ts   => []
```

Values of the type `NETree` can be introduced using copattern syntax, the same one that we have used for defining records.

```
leftmost : (t : NETree A) -> A
| N with t.ts
  | Nil  => t.root
  | Cons => leftmost t.ts.hd
```

Eliminating inductive records is a bit less nice than defining them. As an example, we define the function `leftmost`, which retrieves the leftmost element from `t : NETree`. The default way to define it is to match on `t`. This isn't very informative, because `t` must have been introduced using the constructor `N`, but having matched `t` we can quickly match on `t.ts` using a `with`-clause. The rest of the definition is trivial: if there's no subtrees, we return the `root`, and if there are, we recursively descend to the left subtree, which is the head of hte list of subtrees.

```
leftmost : (t : NETree A) -> A with t.ts
| Nil  => t.root
| Cons => leftmost t.ts.hd

leftmost : (t : NETree A) -> A
with t.ts
| Nil  => t.root
| Cons => leftmost t.ts.hd
```

Note that we have an experimental syntax sugar which allows us to use the `with`-clause without previously matching anything., but I'm not yet sure about its exact form.

```
leftmost : (t : NETree A) -> A :=
  if t.ts is Cons then leftmost t.ts.hd else t.root
```

A much shorter way of defining `leftmost` is to use the `is` syntax for single-case pattern matching. For `leftmost` it works perfectly, resulting in a one-liner, but in general it is not the ultimate solution.

```
leftmost : (t : NETree A) -> A
| N r []        => r
| N _ (t' :: _) => leftmost t'
```

Another possibility to define `leftmost` is to use a more traditional, nested pattern matching on `t` together with its arguments. In case `t.ts` is `[]`, we return the `r`oot. Otherwise, we recursively look for the `leftmost` element of `t'`, the left subtree of `t`.

```
map-net (f : A -> B) : (t : NETree A) -> NETree B
& root => f t.root
& ts   => map map-net t.ts
```

Defining functions into `NETree`s is much easier, as shown in the above example of `map`. We define the fields of the result `NETree` using copattern syntax, while at the same time taking apart the input `NETree` by accessing its fields using dot syntax. Note that the recursive call is `map map-net t.ts`, i.e. we are dealing with higher-order recursion. This is caused by the fact that `t.ts` is a `List` of `NETree`s, so `NETree` itself is a [Nested Inductive Type](#nested-inductive-types).

```
data NEBTree (A : Type) : Type
& root of A
& l r  of Option NEBTree

map (f : A -> B) : (t : NEBTree A) -> NEBTree B
& root => f t.root
& l with t.l
  | None => None
  | Some l' => Some (map l')
& r with t.r
  | None => None
  | Some r' => Some (map r')
```

It is very common for Negative Inductive Types to be Nested Inductive Types. The snippet above defines `NEBTree`, a binary variant of `NETree` in which the two subtrees are wrapped in an `Option`. To define the corresponding `map` function, we need to match on the subtrees using a `with`-clause. As you can see, `NEBTree` is also a Nested Inductive Types, although a simpler one than `NETree`.

```
data BadTree (A : Type) : Type
& root of A
& l r  of BadTree

BadTree-Empty (#A : Type) : (t : BadTree A) -> Empty :=
  BadTree-Empty t.l
```

The reason that Negative Inductive Types are usually nested is that non-nested negative inductives are usually uninhabited. The above snippet defines `BadTree`, a type of non-empty (in the sense of necessarily having an element) binary trees, in which the subtrees are not wrapped in an `Option`. This type, however, turns out to be empty. The reason is that `BadTree` lacks a "base case", so all such trees would have to be of infinite height, but inductive types must be of finite height. Thus, `BadTree` is uninhabited.

```
data NETree (A : Type) : Type
constructor N
& root of A
& subs of ListNETree A

and

data ListNETree (A : Type) : Type
| Nil
| Cons of (hd : NETree A, tl : ListNETree)
```

Besides nesting, another way to make inhabited Negative Inductive Types is to define them mutually with some other types. The above example shows an alternative way of defining `NETree`, mutually inductively with the type `ListNETree`, which is equivalent to `List (NETree A)`. Note that `ListNETree` is an ordinary (i.e. positive) inductive type - mixing positive and negative inductive types in mutual definitions poses no problem.

```
data NETree' (A : Type) : Type
| N of (root : A, ts : List NETree')

root : (t : NETree' A) -> A
| N => t.root

ts : (t : NETree' A) -> List (NETree' A)
| N => t.ts
```

Last but not least, we should note that Negative Inductive Types are not a primitive, built-in feature of our language - they are just syntax sugar for Positive Inductive Types with one constructor. The desugaring of `NETree`, called `NETree'`, is shown in the snippet above. The field accessors are generated automatically.

Not papers:
- [Records in Coq](https://coq.inria.fr/refman/language/core/records.html)
- [Records in Agda](https://agda.readthedocs.io/en/latest/language/record-types.html)

**Status: Coq allows inductive records in addition to native records (i.e. primitive projections) and also allows mutual inductive records (but they must be defined using the `Inductive` keyword). Agda similarly allows defining mutually inductive record types. Mutually defined positive and negative inductives are more suspicious, but since negative inductive can be translated to positive ones, I think this shouldn't pose a problem.**

TODO:
- Finish this section.
- Reconsider the syntax sugar for `with`.

### [Computational Inductive Types](Induction/ComputationalInductiveTypes) <a id="computational-inductive-types"></a> [↩](#toc)

Take a look at the inductive definition below.

```
data Z : Type
| z
| s of (pred : Z)
| p of (succ : Z)
```

This is supposed to be an inductive definition of the type of integers `Z`, very similar in spirit to the definition of `Nat`. There are three constructors: `z` is zero, `s`is successor and `p` is predecessor. But this is not a good definition of `Z`, because it does not represent the integers - there are terms like `s (p z)` which do not correspond to numbers.

However, all is not lost yet - we can endow constructors of inductive types with additional computation rules, which can get rid of the superfluous terms. They are introduced by the `with` keyword, which is followed by a list of constructor arguments, and then we write an ordinary definition by pattern matching (and possibly recursion) in the lines below. To sum up, in our language constructors can compute and types which make use of this feature are called Computational Inductive Types.

```
data Z : Type
| z
| s of (pred : Z) with pred
  | p k => k
| p of (succ : Z) with succ
  | s k => k
```

The above is a proper definition of the type of integers `Z` - the constructors `s` and `p` have associated computation rules, which say that `s (p k)` computes to `k` (this is the rule for `s`) and that `p (s k)` computes to `k` (this is the rule for `p`). This means that the only legal closed normal form terms of type `Z` are `z`, finitely many `s`s applied to `z` and finitely many `p`s applied to `z`. Therefore `Z` is a good representation of the integers.

Note that the computation rules that are allowed for constructors differ a bit from ordinary definitions by pattern matching. First, the patterns need not be exhaustive - if they aren't, no computation takes place. Second, note that we are matching only the constructor arguments and NOT the constructor itself - if the first rule for `s` said `s (p k) => k`, this would be mean it is `s (s (p k))` that reduces to `k`, not `s (p k)`.

```
data Z : Type
| z
| s with (pred : Z)
  | p k => k
| p with (succ : Z)
  | s k => k
```

We also have a tiny syntax sugar: instead of defining constructor arguments in the `of` clause and then using `with` to say which ones we want to match on, we can define new constructor arguments directly in the `with` clause. This means that if we want to match on all arguments of a given constructor, we can drop the `of` completely and define all constructor arguments using `with`, as shown in the example above.

```
abs : Z -> Z
| z   => z
| s k => s k
| p k => s (abs k)
```

We can define functions out of Computation Inductive Types using pattern matching and structural recursion, just like for ordinary inductive types. We only need to handle patterns that correspond to closed terms in normal form - terms that will be "computed away" by constructors' computation rules need not (and cannot) be handled. For `Z` this means that we need to handle `z`, `s k` and `p k`, but we must not handle `s (p k)` or `p (s k)`, and optionally we may separately handle `s z`, `p z` etc.

In the above example we want to compute the absolute value of the argument. For non-negative integers this is easy and we just return the argument, whereas for negative numbers we need to recursively turn predecessors into successors.

See [this file](Induction/ComputationalInductiveTypes/Z.ttw) for a more thorough explanation and exploration of the type of integers defined using Computational Inductive Types and [this directory](Induction/ComputationalInductiveTypes/) for more code on the topic.

#### CITs using Overlapping and Order-Independent Patterns

In a previous version of this section, it was stated that Computational Inductive Types only allow first-match semantics for the additional computation rules. I can't remember why I wrote this, so let's say that for now Overlapping and Order-Independent Patterns are also ok for defining CITs.

```
%OverlappingPatterns
data FM (A : Type) : Type
| in of A
| id
| op with (l r : FM)
  | id    , _  => r
  | op x y, z  => op x (op y z)
  | _     , id => l
```

As an example, consider `FM A`, the type which is the carrier of the free monoid on type `A` (this type is developed in more depth [here](Induction/ComputationalInductiveTypes/FM.ttw)). There are three constructors: `in` for `in`jecting values of type `A` into `FM A`, `id` is the identity element, and `op` is the monoid operation.

`op` has three additional computational rules which guarantee that `op` is associative and `id` is its identity. Note that the last two patterns are overlapping in case `l` is `op x y` and `r` is `id`. This overlap is marked by the `OverlappingPatterns` directive placed above the type declaration, which signalizes that all pattern matching in the type uses the overlapping patterns semantics.

The overlap is fine, because on the one hand we have `op (op x y) id => op x (op y id) => op x y` and on the other hand we have `op (op x y) id => op x y`, so that the right-hand sides are computationally equal if the patterns overlap. The first and third patterns are also overlapping, but it's obvious that this overlap is fine too.

```
data FM (A : Type) : Type
| in of A
| id
%OverlappingPatterns
| op with (l r : FM)
  | id    , _  => r
  | op x y, z  => op x (op y z)
  | _     , id => l
```

If we want to be more granular, we can put the `OverlappingPattern` directive (and its counterpart, `FirstMatch`) directly above the constructor, which makes it apply only to that particular constructor. This way we can mix computational rules based on both `OverlappingPatterns` and `FirstMatch` in a single type.

Papers:
- It turns out that the idea of Computational Inductive Types was invented almost 40 years ago in the language Miranda: [Laws in Miranda](https://sci-hub.se/https://doi.org/10.1145/319838.319839)

**Status: highly experimental. It looks like if we put reasonable constraints on the kinds of computation rules associated with constructors, there isn't any abvious contradiction, nontermination or anything like that. However, there are no prototypes and no papers, except that some Computational Inductive Types can be simulated using [Self Types](https://github.com/uwu-tech/Kind/blob/master/blog/1-beyond-inductive-datatypes.md).**

TODO:
- Come up with more examples of useful Computational Inductive Types.
- Investigate Computational Coinductive Types (for both negative and positive coinductive types).

### [Higher Inductive Types](Induction/HIT) <a id="higher-inductive-types"></a> [↩](#toc)

Higher Inductive Types are inductive types which can be defined using not only point ("ordinary") constructors, but also path constructors which put additional paths into the type. This has two serious uses: the more practical one is for making all kinds of quotients and quotient-like types (and a lot of these can't be made using Computational Inductive Types, because there is no canonical form of some collection of terms) and the more theoretical one is synthetic homotopy theory.

```
data Set (A : Type) : Type
| in of A
| id
| union with (x y : Set)
  | id, y  => y
  | x , id => x
  | union x y, z => union x (union y z)
| comm of (x y : Set) with (i : I)
  | i0 => union x y
  | i1 => union y x
| idem of (x : Set) with (i : I)
  | i0 => union x x
  | i1 => x
| isSet of (x y : Set) (p q : x = y) (i j : I) with i
  | i0 => p j
  | i1 => q j
```

Consider this higher-inductive definition of a set, in the sense of a collection of things of the same type. This type has three point constructors (including one with additional computation rules) and three path constructors (including a two-dimensional one).

The constructor `in` can be used to construct a singleton set (which is an embedding of `A` in `Set`, hence the name), `id` is the empty set (which is the `id`entity of set union, hence the name) and `union` denotes set union. The additional computation rules of `union` guarantee that it is associative and that its neutral element is the empty set `id`.

But with only these three constructors, `Set A` wouldn't be a set at all - the operation of set union must also be commutative (i.e. `union x y = union y x`) and idempotent (i.e. `union x x = x`). This, however, cannot be guaranteed with the point constructors even with additional computation rules, because the term `union x y` does not have a normal form and we cannot in general make `union x x` compute to `x`, because `x` occurs non-linearly in `union x x`.

To deal with this, we have two more constructors, `comm` and `idem`, which create paths `union x y = union y x` and `union x x = x`, respectively. This is done by having an additional constructor argument `i : I` - an element of the abstract interval - which then is declared to compute on its endpoints `i0` and `i1` to the left and right hand sides of the desired equations.

But this still doesn't yield a set, at least not in the sense of Homotopy Type Theory. Because we added so many paths to the type (as many as the powerset of `A`), `Set A` would be a groupoid (or even higher, depending on the h-level of `A`) if not for an additional constructor, `isSet`, which guarantees that all paths in `Set A` are equal.

```
map (f : A -> B) : Set A -> Set B
| in    x           => in (f x)
| id                => id
| union x y         => union (map x) (map y)
| comm  x y     i   => comm  (map x) (map y) i
| idem  x       i   => idem  (map x)         i
| isSet x y p q i j => isSet (map x) (map y) (path i => map (p i)) (path i => map (q i)) i j
```

We can define functions out of higher inductive types by pattern matching. On point constructors, it works as usual - to map a function `f` over a singleton, we apply it to the only element there; to map it over empty set, we return the empty set; and to map it over a union, we map it over each argument of the union.

For path constructors, the rules are similar but a bit more constrained. For `comm x y i`, we must return a generic point on a path between `union (map x) (map y)` and `union (map y) (map x)`. This is because we have mapped the endpoints of `comm`, i.e. `union x y` and `union y x`, to `union (map x) (map y)` and `union (map y) (map x)`, respectively. In practice this means that `comm (map x) (map y) i0` must compute to `union (map x) (map y)` (which it does) and at `comm (map x) (map y) i1` must compute to `union (map y) (map x)` (which it also does). The story for `idem` and `isSet` is analogous, even though for `isSet` it's much harder to mentally check the requirements, because the paths involved are two dimensional. See [this file](Induction/HIT/Set.ttw) for more details on higher-inductive definition of sets.

```
data S1 : Type
| base
| loop with (i : I)
  | i0 => base
  | i1 => base
```

The other use of HITs is to define the various objects studied in homotopy theory, like the homotopical circle shown above. It consists of a single point called `base` and a path from this point to itself, called `base`. Because `S1` is freely generated, what ends up in it is not only the path `loop`, but also also its self-composites like `loop ^ loop`, `loop ^ loop ^ loop`, ..., `loop ^ n`, and also the self-composites of its inverse, `loop ^ -n`.

```
code : S1 -> Type
| base => Z
| loop i => ua equiv-s i

encode (x : S1) (p : base = x) : code x :=
  transport p z

decode : (x : S1) -> code x -> x = base
| base  , z   => refl
| base  , s k => loop ^ decode base k
| base  , p k => loop ^ decode base k
| loop i, k   => ...
```

Having defined the circle, we may go on and use pattern matching to attempt proving that `(base = base) = Z`... but we won't do that, as our main motivation for having HITs in the language is more practical programming rather than doing homotopy theory.

Papers:
- [QUOTIENTS, INDUCTIVE TYPES, & QUOTIENT INDUCTIVE TYPES](https://arxiv.org/pdf/2101.02994.pdf)
- [Type theory in a type theory with quotient inductive types](http://www.cs.nott.ac.uk/~pszgmh/kaposi-thesis.pdf)
- [Constructing Infinitary Quotient-Inductive Types](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC7788612/)
- [Large and Infinitary Quotient Inductive-Inductive Types](https://arxiv.org/abs/2006.11736) (not a very good paper)
- [Quotient inductive-inductive types](https://arxiv.org/abs/1612.02346)
- [Codes for Quotient Inductive Inductive Types](https://akaposi.github.io/qiit.pdf)
- [Constructing quotient inductive-inductive types](https://akaposi.github.io/finitaryqiit.pdf)
- [Quotient inductive-inductive definitions](http://eprints.nottingham.ac.uk/42317/1/thesis.pdf)
- [A model of type theory with quotient inductive-inductive types](http://real.mtak.hu/112971/1/1.pdf)
- [Higher Inductive Types, Inductive Families, and Inductive-Inductive Types](http://von-raumer.de/academic/phd_vonraumer.pdf)
- [A Syntax for Higher Inductive-Inductive Types](https://drops.dagstuhl.de/opus/volltexte/2018/9190/pdf/LIPIcs-FSCD-2018-20.pdf)
- [Signatures and Induction Principles for Higher Inductive-Inductive Types](https://lmcs.episciences.org/6100/pdf)
- [CONSTRUCTING HIGHER INDUCTIVE TYPES AS GROUPOID QUOTIENTS](https://lmcs.episciences.org/7391/pdf)
- [The Construction of Set-Truncated Higher Inductive Types](https://www.sciencedirect.com/science/article/pii/S1571066119301306)
- [Semantics of higher inductive types](https://arxiv.org/abs/1705.07088)
- [Impredicative Encodings of (Higher) Inductive Types](https://arxiv.org/pdf/1802.02820.pdf)
- [On Higher Inductive Types in Cubical Type Theory](https://arxiv.org/pdf/1802.01170.pdf)
- [Mutual and Higher Inductive Types in Homotopy Type Theory](https://paolocapriotti.com/assets/away-day-2014/mhit.pdf)
- [Higher Inductive Types and Internal Parametricity for Cubical Type Theory](https://kilthub.cmu.edu/articles/thesis/Higher_Inductive_Types_and_Internal_Parametricity_for_Cubical_Type_Theory/14555691)

Papers that show how to use HITs for something useful:
- [Free Commutative Monoids in Homotopy Type Theory](https://arxiv.org/pdf/2110.05412.pdf)

**Status: prototype implementations include [cubicaltt](https://github.com/mortberg/cubicaltt), [Cubical Agda](https://agda.readthedocs.io/en/v2.6.0/language/cubical.html), [Arend](https://arend-lang.github.io/) and some other minor languages. No general syntax for HITs is known. Various papers describe subclasses of HITs or HITs combined with induction-induction or something like that. Probably it's very easy to get the most basic and useful HITs, but very hard to get all of them right.**

### [Nominal Inductive Types](Induction/NominalInductiveTypes/CNIC) <a id="nominal-inductive-types"></a> [↩](#toc)

The basics of names and nominal function types are described [here](#names). In this section we only describe how to use nominal features in combination with inductive types to define syntaxes of languages, logics and calculi.

```
data Term : Type
| Var of Name Term
| App of (l r : Term)
| Lam of (body : ∇ α : Term. Term)
```

Representing lambda terms is easy enough. A term is either a variable which is just a name for a term wrapped in the constructor `Var`, an application of one term to another, represented with `App`, or a `Lam`bda abstraction, represented as a term that binds a name.

```
I : Term := Lam (ν α. Var α)

K : Term := Lam (ν α. Lam (ν β. Var α))

S : Term := Lam (ν α. Lam (ν β. Lam (ν γ. App (App (Var α) (Var γ)) (App (Var β) (Var γ)))))
```

Defining `Term`s corresponding to the combinators `I`, `K` and `S` is easy, even though there's a lot of Greek letters and parentheses.

```
I : Term := λ x. x

K : Term := λ x. λ y. x

S : Term := λ x. λ y. λ z. App (App x z) (App y z)
```

Assuming we have a good notation mechanism that fuses `Lam` and `ν x.` into `λ x.` and that `Var` is declared to be a coercion from `Name Term` to `Term`, our lambda terms become very readable.

```
I : Term := λ x. x

K : Term := λ x. λ y. x

S : Term := λ x. λ y. λ z. x z (y z)
```

Assuming we have a really good coercion system that can coerce `t : Term` into `App t : Term -> Term`, our lambda terms can even look like the real lambda terms.

```
subst (t : Term) : (s : ∇ α : Term. Term) -> Term
| ν α. Var α => t
| ν α. Var β => Var β 
| ν α. App (l @ α) (r @ α) => App (subst l) (subst r)
| ν α. Lam (t @ α) => Lam (ν β. subst (ν α. t @ α @ β))
```

To define a function whose domain is a nominal inductive type, we can use recursion and pattern matching, but the pattern matching is a bit more powerful that usually. First, we can match on nominal function types. Second, patterns can have non-linear occurrences of elements of type `Name A`, which effectively means that we can decide equality of names.

This makes it easy to define `subst`itution of the term `t` for the free variable in `s` (`s` is of type `∇ α : Term. Term`, so we can think of it as a term with precisely one free variable). There are four cases:
- `ν α. Var α` - we have encountered the free variable, so we return `t`
- `ν α. Var β` - we have encountered some other variable, so we leave it as is
- `ν α. App (l @ α) (r @ α)` - `s` is an application of `l` to `r`, so we recurse to `subst`itute `t` in `l` and `r`
- `ν α. Lam (t @ α)` - `s` is a lambda, so we descend under the lambda while making sure not to confuse the variable bound by the lambda with the one we are looking for.

For papers, TODOs and the status, see the main section on [Names and Nominal Function Type](#names). The [code directory](Induction/NominalInductiveTypes/CNIC) has extensive examples of how to use nominal inductive types in practice, among others to implement cyclic lists. It also proves some basic properties of names and considers the property of being a `Nameless` type, which turns out to be pretty important in practice.

### Inductive Families <a id="inductive-families"></a> [↩](#toc)

Up until now we were only able to define a single type at a time, or a parameterized family of types in which all the types had the same "structure", just different parameters.

Inductive Families allow us to define an (indexed) family of types in which different types in the family can have different structure, and types with different indices can depend on each other.

```
data Even : Nat -> Prop
| Ez  : Even z
| Ess : (#n : Nat, e : Even n) -> Even (s (s n))
```

The syntax for Inductive Families is similar to that for ordinary inductive types, but with some differences. First, _parameters_ of the family are written before the final colon and they must not be mentioned by constructors, which means they can't vary. **Indices**, on the other hand, are written after the final colon and they may vary between constructors. This means that different constructors' codomains' are potentially different types, which forces us to write them explicitly. The indices (if they are variables) need to be explicitly quantified in every constructor.

The above example shows how to define the predicate `Even` on natural numbers. `Even` has no parameters and one index which is of type `Nat`. There are two constructors: `Ez`, whose type is `Even z`, certifies that zero is an even number, whereas `Ess`, whose type is `(#n : Nat, e : Even n) -> Even (s (s n))`, says that the successor of the successor of an even number is also an even number.

```
add-Even : #(n m : Nat, en : Even n, em : Even m) -> Even (add n m)
| Ez     , _ => em
| Ess en', _ => Ess (add-Even en' em)
```

Functions out of inductive families can be defined as usual, using pattern matching and recursion. The kind of pattern matching we are dealing with here is called **dependent pattern matching**. Note that when we match on something whose type belongs to an inductive family, the index of this thing also "gets matched".

The above example shows how to prove that the sum of two even numbers is even. We match on `en`, the proof of `Even n`. When `en` is matched with `Ez`, we learn that `n`, the index of `en`, **must** be `z`. This means that the goal is computationally equal to `Even (add z m)`, which is computationally equal to `Even m`. Therefore it suffices to use `em` to finish this case of the proof. In the other case, when `en` matches `Ess en'`, we know that the index `n` must be `s (s n')` for some `n'`, so that the goal is `Even (add (s (s n')) m)`, which is computationally equal to `Even (s (s (add n' m)))`, so it suffices to use the constructor `Ess` on the inductive hypothesis (i.e. on the recursive call).

```
add-Even : (n m : Nat, en : Even n, em : Even m) -> Even (add n m)
| .z         , _, Ez         , _ => em
| .(s (s n')), _, @Ess n' en', _ => Ess (add-Even n' m en' em)
```

Above we see the same proof, but this time the arguments `n` and `m` are not implicit. This leads us to notice a new phenomenon that can occur during dependent pattern matching: if a value matches some pattern, this can provide information about what pattern is matched by this value's index. To mark the occurrence of this phenomenon, we use **forced patterns** (which in Agda are called [inaccessible patterns](https://agda.readthedocs.io/en/v2.5.2/language/function-definitions.html#special-patterns)), which consist of a dot followed by an ordinary pattern (possibly in parentheses).

In the above example we match on all four arguments. When `en` matches `Ez`, we know that `n` must be `z`. We mark this by setting the first pattern to be `.z`. Similarly, when `en` matches `@Ess n' en'` (we use the `@` syntax so that we can explicitly name the `n'`), we know that `n` must be `s (s n')` and we mark this by setting the first pattern to be `.(s (s n'))`. Note that for this to be interpreted as a forced pattern, the `s (s n')` must be put in parentheses.

```
One-not-Even : Even (s z) -> Empty
| Ez  impossible
| Ess impossible
```

Another new phenomenon that can occur when we're dealing with dependent pattern matching is that a value might not possibly match a pattern because it has the wrong index. In such a case, we need not provide the right-hand side of the clause - it suffices to use the keyword `impossible`. In the example above, we show that one is not an even number. To do this, we match on the proof of `Even (s z)`. But this proof can't match `Ez`, because its index is `s z`, whereas `Ez` has index `z` which is different from `s z`. Similarly, the proof can't possibly match `Ess`, because the index of `Ess` is `s (s n)` for some `n`, which is different from `s z`. In both cases it suffices to state that this particular case is `impossible`.

```
One-not-Even' : Even (s z) -> Empty
| impossible
```

If we had more impossible cases, writing `impossible` every single time could get boring pretty quickly. If all cases are impossible, we can use the special pattern `| impossible`.

```
Three-not-Even : Even (s (s (s z))) -> Empty
| Ez impossible
| Ess e => One-not-Even' e

Three-not-Even' : Even (s (s (s z))) -> Empty
| Ess e => One-not-Even' e
```

Alternatively, we can also simply omit `impossible` cases when doing pattern matching. The above example shows a proof of the fact that the number three is not even. In the first proof we just say that the `Ez` case is `impossible` and in the `Ess` case we get that one is even, which we already know to be a contradiction. In the second proof, the `Ess` case is the same, but the `Ez` case was omitted - we don't need to handle it.

#### Some problems with indices

```
data Vec (A : Type) : Nat -> Type
| Nil  : Vec z
| Cons : (hd : A, #n : Nat, tl : Vec n) -> Vec (s n)
```

Before we finish this section, let's see the most popular example of an inductive family and the most common problem encountered when dealing with inductive families. This inductive family is `Vec` (short for "vector"), shown above, which represents lists of elements of statically known length.

```
app : #(n1 n2 : Nat) (v1 : Vec A n1) (v2 : Vec A n2) -> Vec A (add n1 n2)
| Nil     , _ => v2
| Cons h t, _ => Cons h (app t v2)
```

The above function, called `app`, concatenates two vectors. It is no big deal - it is almost the same as the `app` we have seen for lists. If it works the same, then appending an empty vector on the right should not change the vector, right? Let's find out.

```
% Fail
app-Nil-r : (#n : Nat) (v : Vec A n) -> app v Nil = v
```

Sadly, we cannot even _state_ the theorem saying that the desired property holds. The reason is a type error: the left-hand side of `app v Nil` has type `Vec A (add n z)`, whereas the right-hand side is of type `Vec A n`. Since the terms `add n z` and `n` are not _computationally_ equal, the types too are not computationally equal, and so we get a type error.

```
add : (n m : Nat) -> Nat
| z   , _ => m
| s n', _ => s (add n' m)
```

The main culprit of this situation (the fact that `add n z` does not compute to `n`) stems from the definition of `add`ition on natural numbers, shown above. But luckily for us, we can get rid of it (and of many other similar problems) using Overlapping and Order-Independent Patterns, mentioned in one of the previous sections.

```
%OverlappingPatterns
add' : (n m : Nat) -> Nat
| z   , _    => m
| s n', _    => s (add n' m)
| _   , z    => n
| _   , s m' => s (add n m')
```

The above definition of `add'` DOES have the property that `add' n z` computes to `n`. Using this definition, we can state (and prove!) our theorems without any problems.

```
app-Nil-r : (#n : Nat) (v : Vec A n) -> app v Nil = v
| Nil      => refl
| Cons h t => path i => Cons h (app-Nil-r t i)
```

The moral of this story is simple: the indices of Inductive Families can often give us a lot of trouble, but in many situations we can make our lives easier with Overlapping and Order-Independent Patterns.

Papers:
- [Pattern Matching Without K](https://jesper.sikanda.be/files/pattern-matching-without-K.pdf)
- [A Syntax for Mutual Inductive Families](https://drops.dagstuhl.de/opus/volltexte/2020/12345/pdf/LIPIcs-FSCD-2020-23.pdf)

**Status: inductive families are standard in proof assistants and dependently-typed languages. Dependent pattern matching is semi-standard, as some languages (notably Coq) have problems with supporting it properly so it's hard to use, while some others (Idris 2 and formerly Agda) have implementations of it that entail Uniqueness of Identity Proofs, which is incompatible with Univalence. The closest implementation of what's described here is probably Agda (with the flag `--without-K`).**

TODO:
- Explicit argument syntax urgently needed in the `head` example above.

### Nested Inductive Families <a id="nested-inductive-families"></a> [↩](#toc)

Nested Inductive Families are inductive families `I` in which the inductive occurrence of `I` in the indices is nested in some type constructor.

```
data Complete : Type -> Type
| E : (#A : Type) -> Complete A
| N : (#A : Type, v : A, ts : Complete (A * A)) -> Complete A
```

A relatively mild example is the type of complete binary trees.

```
map : (#A B : Type, f : A -> B, t : Complete A) -> Complete B
| _, E      => E
| _, N v ts => N (f v) (map (fun (x, y) : A * A => (f x, f y)) ts)
```

Pattern matching and recursion on elements of nested inductive families work as expected. Note that this time the function argument to `map` cannot be a parameter - it must an index instead - because it changes in the recursive call. This is caused by the fact that in the first place the type arguments `A` and `B` cannot be parameters either, because they too change in the recursive call.

```
data Lam : Type -> Type
| Var : (#A : Type, var : Nat) -> Lam A
| App : (#A : Type, l r : Lam A) -> Lam A
| Abs : (#A : Type, body : Lam (Option A)) -> Lam A
```

Another famous nested type is the following representation of lambda calculus terms.

But the two above type families were not that much nested. Things become really interesting only when an occurrence of the type family `I` is nested in itself in one of the indices. Such types are sometimes called Truly Nested Inductive Types.

```
data Bush : Type -> Type
| E : (#A : Type) -> Bush A
| N : (#A : Type, h : A, t : Bush (Bush A)) -> Bush A
```

The most famous example is the following type of `Bush`es. This type is to the the Truly Nested Inductive Families what `List`s are for ordinary inductive types. A `Bush` is either empty (`E`) or is a node (`N`) that consists of a head which is of type `A` and a tail which is a `Bush` of `Bush`es of elements of type `A`.

```
bmap : (#A #B : Type, f : A -> B, b : Bush A) -> Bush B
| E     => E
| N h t => N (f h) (bmap (bmap f) t)
```

As always, let's start (and end) by implementing mapping, here called `bmap`. In the `E` case, we just return `E`. In the `N` case we of course apply `f` to the head of the `Bush`, but for the tail we need to recursively `bmap` the function `bmap f` itself over `t`. This is an example of higher-order recursion in which we have both an indirect recursive call (`bmap f`) and a direct one (`bmap (bmap f)`).

Papers:
- [Deep Induction: Induction Rules for (Truly) Nested Types](https://cs.appstate.edu/~johannp/20-fossacs.pdf)
- [An induction principle for nested datatypes in intensional type theory](https://www.irit.fr/~Ralph.Matthes/papers/MatthesInductionNestedJFPCUP.pdf)

**Status: Nested Inductive Families like `Complete` or `Lam` are supported by Coq and Agda (and probably other languages too). Problems only start with the truly nested types - they are not legal in Coq or Agda, and I would also guess nowhere else. Usually one has to turn off the positivity checker for the definition to be accepted. Even then, support for termination checking, autogeneration of elimination principles and proofs is lacking. To sum up: support for Nested Inductive Families is easy, but support for Truly Nested Inductive Families is very speculative.**

TODO:
- Figure out how the deep induction principles can be implemented in Coq.
- How exactly does termination checking work for truly nested types?
- Decide whether the syntax sugar for families in which codomain indices don't vary should be included in the language.

### Syntax sugar for inductive families with uniform indices <a id='inductive-uniform-indices'></a> [↩](#toc)

In the previous section we have seen a special kind of inductive families, in which the codomain of every constructor had the same index (i.e. the indices only varied in the constructors' arguments) and this index was a variable. We will call such families **families with uniform indices** and we have special syntax sugar to facilitate defining them. It is most useful for nested families, as they are the most common example of families with uniform indices.

The syntax sugar works as follows: whenever an inductive family has uniform indices, we don't need to quantify the codomain index in every constructor separately and we don't need to explicitly provide the codomain - we can use the `of` syntax used for ordinary inductive types, which omits the codomain.

Let's see how the examples from [the previous section](#nested-inductive-families) look like when translated to this new syntax sugar.

```
data Complete : (A : Type) -> Type
| E
| N of (v : A, ts : Complete (A * A))

data Lam : (A : Type) -> Type
| Var of Nat
| App of (l r : Lam A)
| Abs of (body : Lam (Option A))

data Bush : (A : Type) -> Type
| E
| N of (h : A, t : Bush (Bush A))
```

As you can see, we now need to name the index to be able to refer to it, because it is not quantified. Constructor arguments are given after `of` and we omit the codomain, but contrary to ordinary inductive types, we need to explicitly state what the index is for inductive arguments. In the end, the new syntax sugar saves us from quite some typing, especially for longer definitions.

Not papers:
- [Non-regular Parameters are OK](https://gallais.github.io/blog/non-regular-parameters.html) (a blogpost which explains how a translation from uniform indices (i.e. non-uniform parameters) to ordinary inductive families works)

Papers:
- [Semantical Investigations in Intuitionistic Set Theory and Type Theories with Inductive Families](http://www.lsv.fr/~barras/habilitation/barras-habilitation.pdf) (see section 8.6.1)

**Status: Agda and Coq have a similar syntax sugar called _non-uniform parameters_, which is like a dual of our syntax sugar for _uniform indices_. Haskell also supports this, but here it is a full-fledged language feature instead of just syntax sugar. Therefore I think supporting implementing the above syntax sugar for uniform indices would be trivial. Caveat: naive translation from uniform indices to ordinary inductive families raises universe levels, so we need a more elaborate translation (see section 8.6.1 of the above habilitation thesis).**

### A more verbose (and readable) syntax for inductive types <a id="verbose-syntax-for-inductives"></a> [↩](#toc)

There's a more verbose, but also more readable, version of the syntax used for defining inductive types. It should be useful for big types with lots of parameters, constructors, constructor arguments and so on.

```
data List
  parameters
  & A : Type
  sort Type
  eliminator foldl
  constructors
  | []
  | _::_ of (hd : A, tl : List)
```

Above we once more define the type of `List`s using this new syntax. We start with the keyword `data` and the type name, as usual. Then, in the next line, we have the keyword `parameters`, below which we list all the parameters using copattern syntax (i.e. each new line starts with a `&`). One line below that we see the keyword `sort`, which is followed by the universe in which the type lives. Then we have the `eliminator` keyword which lets us create a synonym for the type's elimination principle (the default name, which is available even when we create a synonym, is `typename.elim`). At last, we have the keyword `constructors`, below which we list the constructors, using the familiar syntax where each line starts with a pipe `|`.

```
mutual
  parameters
  & A : Type

  data RoseTree : Type
  | E
  | N of (v : A, ts : RoseTreeList)

  data RoseTreeList
    sort Type
    constructors
    | Nil
    | Cons of (h : RoseTree, t : RoseTreeList)

mutual
  parameters
  & A B : Type
  & f : A -> B

  maprt : (t : RoseTree A) -> RoseTree B
  | E => E
  | N => N (f t.v) (maprtl t.ts)

  maprtl : (ts : RoseTreeList A) -> RoseTreeList B
  | Nil  => Nil
  | Cons => Cons (maprt ts.h) (maprtl ts.t)
```

Besides ordinary inductive types, we also have a version of this verbose syntax for mutual inductive types. Namely, we can use the `keyword` parameters in the line below `mutual` and list the shared parameters there using copattern syntax. The component definitions in these verbose mutual blocks needs not all be verbose themselves - above we show an example mutual definition of `RoseTree` and `RoseTreeList`, in which the `mutual` block and the definition of `RoseTreeList` are both verbose, but the definition of `RoseTree` is ordinary. Note that we can also use these verbose `mutual` blocks for defining mutual recursive functions.

```
data Vec
  parameters
  & A : Type
  indices
  & n : Nat
  sort Type
  constructors
  | Nil  : Vec 0
  | Cons :
    & hd of A
    & #n of Nat
    & tl of Vec n
    -> Vec (s n)
  eliminator foldl
```

Of course we can also use this verbose syntax to define inductive families (indices are declared using copattern syntax below the keyword `indices`), possibly together with copattern syntax for constructor arguments, or any other piece of syntax that we have seen. Above we show how to define the familiar type of `Vec`tors in this syntax. As a bonus, we see how copattern syntax for constructor arguments works for inductive families.

**Status: this is based on Agda's syntax for records, which uses the `constructor` keyword for specifying the constructor name and the `fields` keyword to specify the fields. Using a similar syntax also for inductive types is my own idea, but it should be very easy to implement - it's just syntax.**

TODO:
- Should verbose `mutual` blocks also allow specifying `indices`?

### [Inductive-Inductive Types](Induction/Induction-Induction) <a id="induction-induction"></a> [↩](#toc)

Induction-induction allows us to simultaneously define two or more types such that the later ones can be indexed by the earlier ones.

```
data Dense (R : A -> A -> Prop) : Type
| in  of  (x   : A)
| mid of #(x y : Dense) (H : Dense-R R x y)
| eq  of #(x   : Dense) (H : Dense-R R x x) with (i : I)
  | i0 => mid x x H
  | i1 => in x

and

data Dense-R (R : A -> A -> Prop) : Dense R -> Dense R -> Prop
| in   : #(x y : A) (H : R x y) -> Dense-R (in x) (in y)
| midl : #(x y : Dense R) (H : Dense-R x y) -> Dense-R (mid x y H) y
| midr : #(x y : Dense R) (H : Dense-R x y) -> Dense-R x (mid x y H)
```

In the above example, `Dense-R R` is the dense completion of its parameter relation `R`, which means that it represents the least dense relation that contains `R`. `Dense-R` is defined at the same time as `Dense`, which represents its carrier - the type `A` with added midpoints of all pairs `x, y` such that `R x y`.

Note that the constructors of `Dense` refer to `Dense-R`, the constructors of `Dense-R` refer to constructors of `Dense`, and the indices of `Dense-R` refer to `Dense`. This is characteristic of induction-induction. Also note that `eq` is a path constructor - we may freely mix inductive-inductive types with higher inductive types.

```
mutual
  (R : A -> A -> Prop)

  data Dense : Type
  | in  of A
  | mid of #(l r : Dense) (H : Dense-R l r)
  | eq  of #(x   : Dense) (H : Dense-R x x) with (i : I)
    | i0 => mid x x H
    | i1 => in x

  data Dense-R : (x y : Dense) -> Prop
  | in   of (x is in, y is in, H : R x.in y.in)
  | midl of (x is mid, p : x.r = y)
  | midr of (y is mid, p : x = y.l)
```

Note that inductive-inductive types are not confined to ordinary syntax for inductives - they can use `mutual` blocks, syntax sugar for uniform indices, the `is` syntax for single-case pattern matching, and so on.

```
data BHeap (R : A -> A -> Prop) : Type
| E
| N of (v : A, l r : BHeap, okl : OK R v l, okr : OK R v r)

and

data OK (R : A -> A -> Prop) : A -> BHeap R -> Prop
| OK-E : (v : A) -> OK v E
| OK-N : (v x : A) (l r : BHeap R) (okl : OK x l) (okr : OK x r) -> R v x -> OK v (N x l r)
```

Another classic use of induction-induction is to define data structures with non-trivial invariants (like sorted lists or BSTs). Above, we define the type of binary heaps (ordered by the relation `R`), which can be either `E`mpty, or consist of a `N`ode that holds a `v`alue and two subheaps `l` and `r`, which are `OK`, i.e. satisfy the (one-layer) heap condition, which holds for empty heaps and for nodes whose value is smaller than the values in their subheaps.

Binary heaps could be easily defined even without induction-induction, by first defining binary trees inductively, then the heap condition as an inductive family and finally by putting them together in a dependent record and lifting all binary tree operations to binary heaps. Note, however, that an inductive-inductive definition is so much simpler and more elegant.

```
data BHeap (R : A -> A -> Prop) : Type
| E
| N of
  & root : A
  & l r : BHeap
  & okl : l is N -> R root l.root
  & okr : r is N -> R root r.root
```

Papers:
- [Inductive-inductive definitions](http://www.cs.swan.ac.uk/~csetzer/articlesFromOthers/nordvallForsberg/phdThesisForsberg.pdf)
- [A categorical semantics for inductive-inductive definitions](https://www.cs.nott.ac.uk/~psztxa/publ/catind2.pdf)
- [For Finitary Induction-Induction, Induction is Enough](http://real.mtak.hu/112922/1/paper.pdf)
- [A Finite Axiomatisation of Inductive-Inductive Definitions](https://www.degruyter.com/document/doi/10.1515/9783110324921.259/html)
- [Constructing Inductive-Inductive Types in Cubical Type Theory](https://link.springer.com/chapter/10.1007%2F978-3-030-17127-8_17)

Not papers:
- [Inductive-Inductive Definitions](https://pdfs.semanticscholar.org/5f17/7aaa7559aa8530e64bf59fbb02567a3b16da.pdf) (slides with some examples)
- [Inductive-inductive definitions](https://personal.cis.strath.ac.uk/fredrik.nordvall-forsberg/talks/BCTCS_2010/indind_BCTCS.pdf) (other slides with some other examples)
- Also see the papers on HITs, a lot of which deal specifically with higher inductive-inductive types.

**Status: implemented in Agda, but absent in other mainstream languages. There are many papers which combine it with Higher Inductive Types. Probably not hard to implement. In general, looks good.**

### [Inductive-Recursive Types](Induction/Induction-Recursion) <a id="induction-recursion"></a> [↩](#toc)

Induction-Recursion is an enhancement of inductive types which allows us to mutually define an inductive type `I` and a recursive function of type `I -> D` for some type `D`. There are two common use cases:
- Large induction-recursion: here `D` is `Type`. This flavour of induction-recursion is used for defining closed universes of types.
- Small induction-recursion: here `D` is something  other than `Type`. This flavour of induction-recursion is used for defining data types in a manner similar to induction-induction, but with more computational niceties.

```
data U : Type
| 0
| 1
| +  of (u1 u2 : U)
| *  of (u1 u2 : U)
| →  of (u1 u2 : U)
| pi of (dom : U, cod : El dom -> U)
| eq of (u : U, x y : El u)

and

El : (u : U) -> Type
| 0        => Empty
| 1        => Unit
| u + v    => El u + El v
| u * v    => El u * El v
| u → v    => El u -> El v
| pi u v   => (x : El u) -> El (v x)
| eq u x y => x ={El u} y
```

This is a definition of a universe of codes `U`, which contains codes for the `Empty` type (`0`), the `Unit` type (`1`), sum type (`+`), product type (`*`), function type (`→`), dependent function type (`pi`) and equality type (`eq`). Mutually with `U` we define the function `El` which interprets elements of `U` as ordinary types, i.e. it interprets `0` as `Empty`, `1` as `Unit` and so on. Note that `El` refers to `U` and its constructors (obviously), but also that `U`'s constructors refer to `El`, which is indispensable to correctly represent codes for dependent function type and equality type.

```
data U : Type
| 0
| 1
| + with (u1 u2 : U)
  | 0, u => u
  | u, 0 => u
  | u1 + u2, u3 => u1 + (u2 + u3)
| * with (u1 u2 : U)
  | 0, _ => 0
  | _, 0 => 0
  | 1, u => u
  | u, 1 => u
  | u1 * u2, u3 => u1 * (u2 * u3)
  | u1, u2 + u3 => (u1 * u2) + (u1 * u3)
  | u1 + u2, u3 => (u1 * u3) + (u2 * u3)
| → with (u1 u2 : U)
  | _, 1 => 1
  | 0, _ => 1
  | 1, u => u
  | u1 * u2, u3 => u1 → (u2 → u3)
  | u1 + u2, u3 => (u1 → u3) * (u2 → u3)
  | u1, u2 * u3 => (u1 → u2) * (u1 → u3)
| pi with (dom : U, cod : El dom -> U)
  | 0, _ => 1
  | 1, _ => cod unit
  | u1 * u2, _ => pi u1 (fun x => pi u2 (fun y => cod (x, y)))
  | u1 + u2, _ => pi u1 (fun x => dom (inl x)) * pi u2 (fun y => dom (inr y))
| eq with (u : U, x y : El u)
  | 0     , _       , _        => Unit
  | 1     , _       , _        => Unit
  | u + v , inl x'  , inl y'   => eq u x' y'
  | u + v , inr x'  , inr y'   => eq v x' y'
  | u + v , _       , _        => Empty
  | u * v , (x1, y1), (x2, y2) => eq u x1 x2 * eq v y1 y2
  | u → v , f       , g        => pi u1 (fun x : El u1 => eq u2 (f x) (g x))
  | pi u v, f       , g        => pi u (fun x : El u => eq v (f x) (g x))

and

El : (u : U) -> Type
| 0        => Empty
| 1        => Unit
| u + v    => El u + El v
| u * v    => El u * El v
| u → v    => El u -> El v
| pi u v   => (x : El u) -> El (v x)
| eq u x y => x = y
```

We can combine induction-recursion with Computational Inductive Types to get a more interesting kind of universe - one in which the various type isomorphisms hold by definition. For the boring isomorphisms like `Empty + A = A` this is not very useful (as it's helpful only rarely), but it's extremely useful for the equality type - thanks to Computational Inductive Types we can have `(f = g) = (x : A) -> f x = g x` and `((x1, y1) = (x2, y2)) = (x1 = x2) * (y1 = y2)` and so on.

```
data BHeap (R : A -> A -> Prop) : Type
| E
| N of (v : A, l r : BHeap, okl : OK R v l, okr : OK R v r)

and

OK (R : A -> A -> Prop) (v : A) : (h : BHeap R) -> Prop
| E => Unit
| N => R v h.v
```

Induction-Recursion, just like Induction-Induction, can also be used to define data structures with complex invariants. Above we have the binary heaps again, but this time the (non-recursive) heap condition is defined by pattern matching mutually with the type of binary heaps.

Papers:
- [A General Formulation of Simultaneous Inductive-Recursive Definitions in Type Theory](https://www.cse.chalmers.se/~peterd/papers/Inductive_Recursive.pdf)
- [A Finite Axiomatization of Inductive-Recursive Definitions](https://www.cse.chalmers.se/~peterd/papers/Finite_IR.pdf)
- [Induction-Recursion and Initial Algebras](https://www.cse.chalmers.se/~peterd/papers/InductionRecursionInitialAlgebras.pdf)
- [Indexed induction–recursion](https://www.sciencedirect.com/sdfe/reader/pii/S1567832605000536/pdf)
- [Small Induction Recursion](https://www.cs.nott.ac.uk/~psztxa/publ/tlca13-small-ir.pdf)
- [Containers, monads and induction recursion](https://sci-hub.se/10.1017/s0960129514000127)
- [Positive Inductive-Recursive Definitions](https://arxiv.org/pdf/1502.05561.pdf)
- [Variations on Inductive-Recursive Definitions](https://strathprints.strath.ac.uk/62321/1/Ghani_etal_MPCS_2017_Variations_on_inductive_recursive.pdf)
- [Fibred Data Types](https://www.researchgate.net/publication/261165437_Fibred_Data_Types)

Tangentially related:
- [Higher inductive-recursive univalence and type-directed definitions](https://homotopytypetheory.org/2014/06/08/hiru-tdd/) - see for a definition of universe with type-directed equality like the one presented above, but using higher-inductive types instead of computational inductive types
- [Simulating Induction-Recursion for Partial Algorithms](https://members.loria.fr/DLarchey/files/papers/TYPES_2018_paper_19.pdf) - how to define complicated recursive functions without resorting to induction-recursion
- [A polymorphic representation of induction-recursion](https://www.researchgate.net/publication/244448805_A_polymorphic_representation_of_induction-recursion) (also see the [slides](http://www.cs.ru.nl/dtp11/slides/capretta.pdf))
- [A Formalisation of a Dependently Typed Language as an Inductive-Recursive Family](https://www.cse.chalmers.se/~nad/publications/danielsson-types2006.pdf)

Generic programming using (inductive-recursive) universes:
- [Fully Generic Programming Over Closed Universes of Inductive-Recursive Types](https://pdxscholar.library.pdx.edu/cgi/viewcontent.cgi?article=4656&context=open_access_etds) - generic programming with universes
- [Generic functional programming](https://gitlab.inria.fr/fpottier/mpri-2.4-public/blob/8485cc50346803d661e1ea4c5b8e485ccad18f66/agda/04-generic/Desc.lagda.rst)

**Status: induction-recursion is implemented in Agda and in Idris 1 (or at least this is what Wiki claims), and there was an experimental branch of Coq that implemented it a long time ago. In general, however, it is not mainstream. Implementation should not be problematic.**

## [Recursive Families](Induction/IndicesThatCompute) <a id="recursive-families"></a> [↩](#toc)

We have previously seen how to define `Vec` as an inductive family, but this is not the only way. Consider an alternative representation of vectors, defined by recursion on the index `n`.

```
RVec (A : Type) : Nat -> Type
| z   => Unit
| s n => (hd : A, tl : RVec n)
```

We can then define vectors as follows.

```
// The empty vector.
x : RVec Nat 0 := unit

// Singleton vector.
y : RVec Nat 1 := (hd => 42, tl => unit)

// Shorter syntax.
y' : RVec Nat 1 := (42, unit)

// A longer example.
z : RVec Nat 5 := (0, (1, (2, (3, (4, unit)))))
```

We may now ask ourselves: which representation is better: the inductive one or the recursive one? Let's start by listing the pros and cons of each representation.

|                        | Inductive families     | Recursive families     |
| ---------------------- | ---------------------- | ---------------------- |
| Notation               | intuitive              | less intuitive         |
| Uniqueness principle   | no                     | inherited from records |
| Pattern matching       | yes                    | only on the index      |
| Structural recursion   | yes                    | only on the index      |
| Forcing & detagging    | if the compiler has it | yes                    |
| Large indices          | no                     | yes                    |
| Non-indexed types      | yes                    | no                     |
| Non-positive types     | no                     | yes                    |

As for the notation, the usual notation for defining inductive types is better, because people are used to it, whereas defining types by recursion is uncommon even in dependently-typed languages where it is possible. Moreover, the recursive definition has ugly consequences, like having to write `unit` instead of `Nil` and lots of parenthesis instead of `Cons`.

Next, `Vec` is an inductive family and thus has no uniqueness principle, i.e. if we have `x y : Vec A 0`, then we need to match `x` and `y` to find out that they are both `Nil`. This is not the case for `RVec`, because for `RVec A 0 ≡ Unit` and `Unit` is a strict proposition, so for all `x y : RVec A 0` we have `x ≡ y`. Similarly, for `x : RVec A (s n)` we have `x ≡ Cons x.hd x.tl` (note: assuming a uniqueness principle for single-constructor extensible sums).

Another difference between the two representations is the use of pattern matching and recursion to define functions on vectors. With the inductive vectors, all is as usual, with dependent pattern matching fully supported. For `RVec`, however, pattern matching and recursion is only supported for the index. To match the value itself, we have to match the index first. The difference is very small, but annoying.

```
vmap (f : A -> B) : Vec A n -> Vec B n
| Nil      => Nil
| Cons h t => Cons (f h) (vmap t)

rmap (f : A -> B) : (#n : Nat) -> RVec A n -> RVec B n
| z   , unit   => unit
| s n', (h, t) => (f h, rmap t)
```

As for forcing and detagging: the inductive `Vec` needs to store its index `n` somehow, and the index also appears as one of the arguments of `Cons`. This is not a problem as long as we're only concerned with proving, but as soon as we're interested in performance or extraction to another language, it starts being problematic. The recursive `RVec`, on the other hand, doesn't have the same problems - the index is an input from which the type is computed, so we don't need to store it.

As for large indices and non-strictly-positive types: inductive types have to conform to strict rules about which universe they can live in. For example, the universe of an inductive type must be at least as big as the universe of all its arguments. This is required to ensure that we can't use the mechanism of inductive definitions to lower the universe level of some other type just by wrapping it in an inductive. Inductive types also need to conform to strong rules regarding positivity - inductive arguments can't occur in negative positions (i.e. to the left of an odd number of arrows), because such types are contradictory thanks to Cantor's theorem. Occurrences which are positive but not strictly positive are also not allowed, as they may result in a proof of `Empty` in some cases. Recursive types, on the other hand, don't have to observe the same rules - we can do anything we want, as long we're doing it by recursion on the index.

The final difference between the two representation is that inductive types allow us to define types which are not indexed, like the natural numbers, whereas recursive types do not, because if there is no index, there is nothing to do recursion on.

To sum up, inductive and recursive definitions are applicable mostly in different scenarios: inductives to ordinary types and type families which can't be defined by recursion on the indices, recursives to types with large indices or non-strictly-positive types. The only point of overlap are indexed families which can be defined by recursion on the indices. In this case, the comparison is kind of a draw: recursive families have more benefits, like uniqueness principle and forcing/detagging, but they suffer from bad notation for defining the type, its values and functions out of it. If only the notation wasn't so bad...

This is why we introduce syntax sugar for recursive families!

```
rectype RVec (A : Type) : Nat -> Type
| Nil  : RVec z
| Cons : (hd : A, #n : Nat, tl : RVec n) -> RVec (s n)
```

The above is a definition of the recursive family `RVec` in a syntax very close to that of inductive families. The only difference is that we use the keyword `rectype` instead of `data`. This definition is desugared as follows.

```
RVec (#A : Type) : Nat -> Type
| z   => [Nil]
| s n => [Cons (hd : A, tl : RVec n)]
```

This is a recursive definition of `RVec` very close to what we have seen at the beginning of this section, but instead of the `Unit` type we use the single-constructor extensible sum type `[Nil]` and instead of using the bare record `(hd : A, tl : RVec n)` we wrap it in a single-constructor extensible sum with the constructor named `Cons`.

```
// Definitions of the same x, y and z as above.
x : RVec Nat 0 := Nil
y : RVec Nat 1 := Cons 42 Nil
z : RVec Nat 5 := Cons 0 (Cons 1 (Cons 2 (Cons 3 (Cons 4 Nil))))
```

Thanks to the clever use of extensible sums, we can now define vectors in a notation that is identical to that of inductive families. But what about functions on vectors?

```
rmap' (f : A -> B) : RVec A n -> RVec B n
| Nil      => Nil
| Cons h t => Cons (f h) (rmap' t)
```

We can introduce another piece of syntax sugar which allows us to match only on the `RVec` and omit dealing with the index. This is desugared to the code below.

```
rmap' (f : A -> B) : (n : Nat) -> RVec A n -> RVec B n
| z   , Nil      => Nil
| s n', Cons h t => Cons (f h) (rmap' n' t)
```

Because we can infer the index from the constructor (`Nil` corresponds to `z` and `Cons` to `s n`), our syntax sugar can be desugared by translating the index-omitting pattern matching in `rmap'` to the full pattern matching as in the original `rmap` (with the difference being that we retain the nice constructor names `Nil` and `Cons`, instead of the ugly `unit` and `(,)`).

With this syntax sugar, recursive families emerge as the clearly superior solution for defining indexed families whenever it is possible to do this by recursion on the indices.

Papers:
- [Vectors are records, too](https://jesper.sikanda.be/files/vectors-are-records-too.pdf) (also see [the slides](https://jesper.sikanda.be/files/TYPES2018-presentation.pdf)) - this is the paper on which most of this section is based
- [A simpler encoding of indexed types](https://arxiv.org/pdf/2103.15408.pdf)

**Status: very wild speculations, but it looks pretty reasonable - it's just another piece of syntax sugar. The uniqueness principle for single-constructor extensible sums may be problematic, but I think it would be doable.**

TODO:
- Think about this more.
- Figure out what nonstandard techniques are allowed by having [manifest fields in constructors](Induction/IndicesThatCompute/IndicesThatCompute.ttw).

## [Coinductive Types](Coinduction) <a id="coinductive-types"></a> [↩](#toc)

The syntax of coinductive type definitions is supposed to be dual to that of inductive types - as dual as possible, but not more. The closest to what we have is probably Agda. Just as for inductives, we reduce the amount of bookkeeping and boilerplate by allowing the same field names in multiple types and by giving each coinductive type its own namespace. All the usual restrictions apply, i.e. only strictly positive types are allowed.

The basic coinductive types are negative, i.e. they are possibly self-referencing records. Corecursive functions (and also just values of coinductive types) are defined by copattern matching. They must be productive and the copattern matching needs to cover all possible cases. The semantics of copattern matching are more akin to the semantics of traditional pattern matching than to the Overlapping and Order-Independent Patterns semantics that we use as our main semantics of pattern matching. A definition by copattern matching can optionally begin by giving a prototype of the result (which must be a value of the same coinductive type) and then further fields of the result are given or fields coming from the prototype are modified.

In addition to basic coinductive types, which can have parameters or be defined mutually with other coinductive types, we have special support for Nested Coinductive Types (the productivity checker can recognize productivity of higher-order corecursive calls). We also support true coinductive families, which are exactly dual to inductive families, nested coindcutive families, and other advanced forms of coinductive types.

Besides negative coinductive types, we also support positive coinductive types. These are defined by giving their constructors and eliminated using pattern matching, just like inductive types. However, positive coinductive types fundamentally are just a syntax sugar that is desugared to an inductive base functor and the knot is tied with a negative coinductive types.

### Negative Coinductive Types <a id="negative-coinductive-types"></a> [↩](#toc)

Coinductive types are "negative", i.e. they are record-like types which are defined by specifying what fields they have. Definitions of coinductive types start with the keyword `codata`. Then, in separate lines starting with `&`, we list field names and their types. Below we define a coinductive product type whose left projection is `l` and right projection is `r`.

```
codata _*_ (A B : Type) : Type
& l of A
& r of B
```

Functions whose codomain is coinductive are defined by copattern matching. The fields of a coinductive value can be accessed with the dot notation, just like for records.

```
swap (x : A * B) : B * A
& l => x.r
& r => x.l
```

We can also unpack/open the argument if we want a shorter way of referring to its fields.

```
swap (x : A * B) : B * A :=
open x in
& l => r
& r => l
```

But things are even more comfortable: coinductive values are unpacked for us automatically and we only need to use the dot notation in case of ambiguity.

```
swap (x : A * B) : B * A
& l => r
& r => l
```

Of course the coinductive type being defined can appear in types of fields, provided that it stands in a strictly positive position. Note that the distinction between parameters and indices we introduced for inductive types also applies to coinductive types, so we only need to write `Stream` instead of `Stream A`.

```
codata Stream (A : Type) : Type
& hd of A
& tl of Stream
```

Corecursive definitions by copattern matching work essentially the same as those which are not corecursive. Note that, just like for recursive definitions, we must omit the parameters of the definition, which may look weird at first and requires some getting used to.

```
map (f : A -> B) : (s : Stream A) -> Stream B
& hd => f s.hd
& tl => map s.tl
```

Definitions by copattern matching, just like those by ordinary pattern matching, can make use of nested copatterns that describe the deeper structure of the result.

```
interleave : (l r : Stream A) -> Stream A
& hd    => l.hd
& tl hd => r.hd
& tl tl => interleave l.tl r.tl
```

The above definition is equivalent to the following one which doesn't use deep copatterns.

```
interleave : (l r : Stream A) -> Stream A
& hd => l.hd
& tl => interleave r l.tl
```

In case of extremely deep copatterns, the syntax might get heavy due to repetitions of field names. We can deal with that by modularising our copatterns a bit.

```
interleave : (l r : Stream A) -> Stream A
& hd => l.hd
& tl
  & hd => r.hd
  & tl => interleave l.tl r.tl
```

There's also an underscore copattern `_`, which is somewhat dual to the catch-all pattern `_` - we can use it for prototyping/prototypical inheritance, i.e. something like "take definitions of all the fields that I didn't mention so far from the right-hand side".

We can also use copattern matching to define functions whose codomain is not coinductive, but only built up from coinductive types. This is easiest to understand with an example.

```
split : (s : Stream A) -> Stream A * Stream A
& l hd => s.hd
& r hd => s.tl.hd
& _ tl => split s.tl.tl
```

In pattern matching, `_` ignores a part of the argument we are matching. In copattern matching, `_` can be interpreted as syntax sugar which desugars by transforming both the left-hand side and the right-hand side of a clause by inserting all fields that we omitted.

```
split : (s : Stream A) -> Stream A * Stream A
& l hd => s.hd
& r hd => s.tl.hd
& l tl => (split s.tl.tl).l
& r tl => (split s.tl.tl).r
```

We can combine copattern matching with pattern matching. Below we define a function `streamize (x : A) : List A -> Stream A` that turns a list into a stream - once we run out of list elements, the rest of the stream is all `x`s. In this definition, our copatterns match the output (of type `Stream A`), whereas the patterns match the input (of type `List A`).

```
streamize (x : A) : List A -> Stream A
& hd | []     => x
& tl | []     => streamize []
& hd | h :: _ => h
& tl | _ :: t => streamize t
```

We should interpret this definition as follows:
- the head of the output stream is `x` when the input is `[]`
- the tail of the output stream is `streamize []` when the input is `[]`
- the head of the output stream is `h` when the input is `h :: _`
- the tail of the output stream is `streamize t` when the input is `_ :: t`

The grouping of the copatterns and patterns doesn't matter much (besides aesthetics). The definition below, in which the second and third clauses are swapped, is computationally equal to the previous one.

```
streamize (x : A) : List A -> Stream A
& hd | []     => x
& hd | h :: _ => h
& tl | []     => streamize []
& tl | _ :: t => streamize t
```

In case we feel the syntax is getting too heavy, we can combine our copatterns and patterns in a way similar to what we did for nested copatterns. The function below is computationally equal to the above ones.

```
streamize (x : A) : List A -> Stream A
& hd
  | []     => x
  | h :: t => h
& tl
  | []     => streamize []
  | _ :: t => streamize t
```

But we cannot mix the order of patterns and copatterns, because the order decides whether the function is recursive or corecursive. If we start with pattern matching, the function is recursive. If we start with copattern matching, the function is corecursive. For example, the function below, which starts with patterns, is supposed to be recursive, but because of this it is illegal: `streamize []` is not a valid recursive call.

```
streamize (x : A) : List A -> Stream A
| []
  & hd => x
  & tl => streamize []
| h :: t
  & hd => h
  & tl => streamize t
```

Last but not least, definitions by copattern matching can use `with`-clauses to perform pattern matching on intermediate expressions.

```
findAndReplace (p : A -> Bool) (x : A) : (s : Stream A) -> Stream A
& hd with p s.hd
  | tt => x
  | ff => s.hd
& tl => findAndReplace s.tl
```

The above use of a `with`-clause if equivalent to the following use of an `if-then-else` expression.

```
findAndReplace (p : A -> Bool) (x : A) : (s : Stream A) -> Stream A
& hd => if p s.hd then x else s.hd
& tl => findAndReplace s.tl
```

Papers:
- [Copatterns Programming Infinite Structures by Observations](https://www.researchgate.net/profile/Anton-Setzer/publication/262366004_Copatterns_Programming_Infinite_Structures_by_Observations/links/587fe0f208ae9275d4ee3ae2/Copatterns-Programming-Infinite-Structures-by-Observations.pdf)
- [Unnesting of Copatterns](http://www2.tcs.ifi.lmu.de/~abel/rtatlca14.pdf) (also see the [slides](https://pdfs.semanticscholar.org/cc02/dfbc9f281ddfaea8065ca9c3ac5862979bab.pdf))
- [Wellfounded Recursion with Copatterns and Sized Types](http://www2.tcs.ifi.lmu.de/~abel/jfp15.pdf)
- [Copattern matching and first-class observations in OCaml, with a macro](https://hal.inria.fr/hal-01653261/document)

Not papers:
- [Pattern and Copattern matching](http://www1.maths.leeds.ac.uk/pure/logic/images/slidesLeedsLogicSeminarMay2015.pdf)

**Status: negative inductive types are imeplemented in Agda and Coq. Additionally, copattern matching is implemented in Agda. The Agda implementation of copatterns is based on one of the papers, which means things look pretty good.**

TODO:
- Maybe if we start with patterns, then the definition should still be interpreted as legal corecursive definition?
- Invent Overlapping and Order-Independent Copatterns.
- Another possibility for handling coinductives is for them to be just (co)recursive records, but this depends on how cool and strange records will be.
- Mention the usage of `@` to name subcopatterns. This should be dual to using `@` in pattern matching to name subpatterns.

### Positive Coinductive Types <a id="positive-coinductive-types"></a> [↩](#toc)

We have special syntax for coinductive types that have only a single field which is a sum. Examples include colists, conatural numbers and so on.

```
codata CoList (A : Type) : Type
| CoNil
| CoCons of (hd : A, tl : CoList)
```

The above is a definition of a type of colists, i.e. things which are like lists, but possibly infinite. In fact, it is a definition of a parameterized family of coinductive types. The type has two constructor, `CoNil` and `CoCons`, whose arguments are just like those for `List`s.

Note that the above is NOT an inductive type, despite using the `|` syntax of inductive types, and also not an ordinary coinductive type like those we saw in the previous section. The above is just a syntax sugar that desugars to the following ordinary coinductive type definition.

```
data CoListX (X A : Type) : Type
| CoNilX
| CoConsX of (hd : A, tl : X)

codata CoList (A : Type) : Type
& Out of CoListX CoList A

CoNil : CoList A
& Out => CoNilX

CoCons (h : A) (t : CoList A) : CoList A
& Out => CoConsX h t
```

We can use pattern matching on values of such single-field coinductive types as if their type was inductive. Additionally, we can omit copattern matching when defining functions into such types, as there is only one field anyway. These two features can be combined.

```
app : (l1 l2 : CoList A) -> CoList A
| CoNil     , _ => l2
| CoCons h t, _ => CoCons h (app t l2)
```

To desugar this definition, we need to add the single-field copattern at the top level, replace patterns refering to "constructors" of `CoList` with patterns taht refer to constructors of `CoListX`, and turn naked uses of colists (i.e. `l : CoList A`) into uses of their field (i.e. `l.Out : CoListX (CoList A) A`).

```
app : (l1 l2 : CoList A) -> CoList A
& Out with l1.Out, l2.Out
  | CoNilX     , _ => l2.Out
  | CoConsX h t, _ => CoConsX h (app t l2)
```

Use of overlapping (and order-independent) patterns is of course allowed when using this syntax sugar.

```
app : (l1 l2 : CoList A) -> CoList A
| CoNil     , _     => l2
| _         , CoNil => l1
| CoCons h t, _     => CoCons h (app t l2)
```

The above definition gets desugared to the one below, which uses overlapping patterns.

```
%OverlappingPatterns
app : (l1 l2 : CoList A) -> CoList A
& Out
  | CoNilX     , _      => l2.Out
  | _          , CoNilX => l1.Out
  | CoConsX h t, _      => CoConsX h (app t l2)
```

See [the file dealing with conatural numbers](Coinduction/Conat.ttw) for more details on this notation.

Papers:
- None, this is my idea.

**Status: somewhat experimental. There are no papers nor a prototype implementation. However, it looks pretty reasonable and I have some Coq code [here](Coinduction/Code/CoVec.v) that shows an example manual desugaring.**

TODO:
- Write some (pseudo)code that uses this to get comfortable with it.

TODO:
- Look for papers.

### Various syntactic conveniences for coinductive types <a id="syntactic-conveniences-for-coinductives"></a> [↩](#toc)

Names of coinductive type fields do NOT need to be globally unique, unlike in many other languages - multiple types can have fields with the same names.

```
codata NonEmptyCoList (A : Type) : Type
& hd of A
& tl of Option NonEmptyCoList
```

The above type defines the type of non-empty colists. The fields are named `hd` and `tl`, just like the fields of `Stream`, but this does not produce much confusion. When accessing a field, like `s.hd`, it is clear from the type of `s` which `hd` is meant. This is the case also in many other situations. If `hd` is truly ambiguous, we can disambiguate by writing `Stream.hd` and `NonEmptyCoList.hd`, respectively. Here `Stream` and `NonEmptyCoList` are not type names, but instead the namespaces associated to these types - every coinductive type has an associated namespace.

```
codata CoList (A : Type) : Type
| Nil
| Cons of (hd : A, tl : CoList)
```

The above code defines the type of colists again, but this time with constructor names changed to `Nil` and `Cons`. The constructor names are the same as for lists, but we don't need to worry about name conflicts, neither with inductive types nor with other positive coinductive types (not with negative coinductive types' field names), because positive coinductive types have their own associated namespaces too.

```
> :t NonEmptyCoList.hd
NonEmptyCoList.hd : (#A : Type) -> NonEmptyCoList A -> A

> :t NonEmptyCoList.tl
NonEmptyCoList.tl :
  (#A : Type) -> NonEmptyCoList A -> Option (NonEmptyCoList A)

> :t CoList.Nil
CoList.Nil : (#A : Type) -> CoList A

> :t CoList.Cons
CoList.Cons : (#A : Type, hd : A, tl : CoList A) -> CoList A

> :def CoList.Nil.args
CoList.Nil.args : Type := (A : Type) -> ()

> :def CoList.Cons.args
CoList.Cons.args : Type := (A : Type) -> (hd : A, tl : CoList A)

> :def NonEmptyCoList.params
NonEmptyCoList.params : Type := (A : Type)

> :def CoList.params
CoList.params : Type := (A : Type)

> :t NonEmptyCoList.constructor
NonEmptyCoList.constructor :
  (#A : Type, hd : A, tl : NonEmptyCoList A) -> NonEmptyCoList A
```

Just like for inductive types, each coinductive type has its own namespace. There, we can find fields (for negative coinductives) and constructors and constructor arguments (for positive coinductives), type parameters, and also the constructor for negative coinductive types. There's also an `Extra` subnamespace just as for inductives, even though it's not shown in the listing above.

```
codata CoList (A : Type) : Type
| Nil
| Cons of
  & hd of A
  & tl of CoList

app : (l1 l2 : CoList A) -> CoList A :=
  fun l1 l2 => if l1 is Cons h t then Cons h (app t l2) else l2

codata Sum (A B : Type) : Type
| inl of A
| inr of B
```

For positive coinductive types, we may use all the syntactic conveniences we know from inductive types, like the `is` syntax for single-case pattern matching, copattern syntax for constructor arguments and the syntax sugar for single-argument constructors.

```
codata StreamOfPositives : Type
& hd of Nat
& hd is s
& tl of StreamOfEvens

codata CoListOfPositives : Type
| Nil
| Cons of (hd : Nat, hd is s, tl : CoListOfPositives)
```

Just as for inductives, we can have unnamed constructor arguments for positive coinductive types, provided that the field's type is a proposition that can be decided and inferred automatically. But there's more: we can also use unnamed fields in definitions of negative coinductive types. The above snippet shows definitions of a stream of positive naturals and a colist of positive naturals.

```
zipWith (f : A -> B -> C) : (s1 : Stream) -> (s2 : Stream) -> Stream
& hd => f s1.hd s2.hd
& tl => zipWith s1.tl s2.tl
```

The _bundled parameters syntax_ that we saw previously used with inductive types, also works with coinductive types. In the above implementation of `zipWith`, we don't specify what is the type of elements of the `Stream`s, but what gets inferred is `s1 : Stream A` (because we use `s1.hd` as the first argument of `f`) and `s2 : Stream B` (because we use `s2.hd` as the second argument to `f`), and the result is inferred to be `Stream C`, because this is the type of `f s1.hd s2.hd` which we used for the `hd` of the result. The equivalent code that doesn't use the bundled parameters syntax is

```
zipWith (f : A -> B -> C) : (s1 : Stream A) -> (s2 : Stream B) -> Stream C
& hd => f s1.hd s2.hd
& tl => zipWith s1.tl s2.tl
```

Last but not least, the bundled parameters syntax of course also works with positive coinductive types.

```
codata CoNat : Type
| z
| s of (pred : CoNat)

len : (l : CoList) -> CoNat
| Nil  => z
| Cons => s (len l.tl)
```

Papers:
- None.

**Status: non-unique field names for coinductives are analogous to non-unique constructor names for inductives. Coinductive namespacing is analogous to inductive namespacing, which is implemented in Lean. The `is` syntax shouldn't pose problems, as it can be desugared to pattern matching, which is then desugared to copattern matching on negative coinductive types. Copattern syntax for constructor arguments and the syntax sugar for single-argument constructors should work fine provided they work for inductive types. Bundled parameter syntax is very speculative.**

### Nested Coinductive Types <a id="nested-coinductive-types"></a> [↩](#toc)

Just as inductive types can be nested, leading to higher-order recursion, so can be coinductive types, leading to higher-order corecursion. This applies to both negative and positive coinductive types.

```
codata StreamTree (A : Type) : Type
& v  of A
& ts of Stream StreamTree
```

Above we have an example of nested (negative) coinductive types. `StreamTree`, is a necessarily infinite tree that has a value `v : A` at its root and a `Stream` of subtrees. This type is nested, because `StreamTree` occurs as an argument to `Stream`.

```
stmap (f : A -> B) : (t : StreamTree A) -> StreamTree B
& v  => f t.v
& ts => map stmap t.ts
```

We can define the mapping function (called `stmap` to distinguish it from mapping functions for other types) on `StreamTree`s as above. For the field `v`, we just apply `f` to `t.v`. For the subtrees `ts`, however, we can't directly make any corecursive calls - we need to `map` the function `stmap` over the `Stream` of subtrees. This is an example of higher-order corecursion.

```
stmap (f : A -> B) : (t : StreamTree A) -> StreamTree B
& v  => f t.v
& ts
  & hd => stmap t.ts.hd
  & tl => (stmap (t.v, t.ts.tl)).ts
```

Another, less nice way of defining this function is to use direct corecursion. Above, we defined the head of the `Stream` of subtrees using a recursive call on `t.ts.hd` and then we use another corecursive call, this time on `(t.v, t.ts.tl)`, which is a `StreamTree` with the same `v` as the original, but with a "shorter" stream, to define the tail of the `Stream` of subtrees. This is ugly, but works.

```
stmap (f : A -> B) : (t : StreamTree A) -> StreamTree B
& v  => f t.v
& ts => smap t.ts

and

smap (f : A -> B) : (s : Stream (StreamTree A)) -> Stream (StreamTree B)
& hd => stmap s.hd
& tl => smap s.tl
```

Yet another way to define this function is to split it into two mutually corecursive functions. Above, we define `stmap` corecursively by referring to `smap`, a mapping function on `Stream`s of `StreamTree`s, and at the same time we define `smap` corecursively by referring to `stmap`.

```
codata CoRoseTree (A : Type) : Type
| Empty
| Node of (v : A, ts : CoList CoRoseTree)
```

`CoRoseTree`, shown above, is an example of a nested (positive) coinductive type. It is a coinductive version of `RoseTree` that we saw in the section on nested inductive types, but with a `CoList` of subtrees instead of a `List`. It is a nested type, because `CoRoseTree` occurs as an argument to `CoList`.

```
crmap (f : A -> B) : CoRoseTree A -> CoRoseTree B
| Empty     => Empty
| Node v ts => Node (f v) (map crmap ts)
```

Implementing a mapping function (called `crmap`) for `CoRoseTree` poses more or less the same challenges as implementing it for `StreamTree`. One way to do it, shown above, is to use higher-order recursion, `map`ping the `crmap` over the colist of subtrees.

```
crmap (f : A -> B) : CoRoseTree A -> CoRoseTree B
| Empty => Empty
| Node v l with l =>
  | Nil      => Node (f v) Nil
  | Cons h t with crmap (Node v t)
    | Empty => Node (f v) (Cons (crmap h) Nil)
    | Node v' t' => Node v' (Cons (crmap h) t')
```

Another way, much uglier, is to kind of "inline" the `map` in the definition of `crmap`, as shown above. However, this way is a little problematic, as we also need to pattern match on the result of the corecursive call `crmap (Node v t)` so that we can properly attach the first subtree, which is `crmap h`. This is not a pleasant way to define `crmap`.

```
crmap (f : A -> B) : CoRoseTree A -> CoRoseTree B
| Empty    => Empty
| Node v l => Node (f v) (clmap l)

and

clmap (f : A -> B) : CoList (CoRoseTree A) -> CoList (CoRoseTree B)
| Nil      => Nil
| Cons h t => Cons (crmap h) (clmap t)
```

The last possibility, just like for `StreamTree` previously, is to split the definition of `crmap` into two mutually corecursive definitions, one of `crmap` proper and the other of `clmap`, a mapping function on `CoList`s of `CoRoseTree`s.

Papers:
- None.

**Status: nested coinductive types are not standard. Indeed, they are not really supported in Coq, no matter how hard I try, and I guess also not in Agda nor other proof assistants.**

TODO:
- Search for papers.
- Think more about how productivity is checked.
- Come up with a translation of Nested Coinductive Types to Mutual Coinductive Types.

### Mutual Coinductive Types <a id="mutual-coinductive-types"></a> [↩](#toc)

In the previous section we have seen that we can translate higher-order corecursion on `StreamTree` and `CoRoseTree` into mutual recursion. This translation is justified by the fact that we could have just as well defined these types as Mutual Coinductive Types. The mechanism of Mutual Coinductive Types allows us to simultaneously define many coinductive types which can refer to each other, analogously to how Mutual Inductive Types work.

```
codata StreamTree (A : Type) : Type
& v  of A
& ts of StreamOfStreamTree

and

codata StreamOfStreamTree (A : Type) : Type
& hd of StreamTree
& tl of StreamOfStreamTree
```

The above code shows how to mutually define the type of `StreamTree`s and `StreamOfStreamTree`, which is just `Stream` specialized to hold `StreamTree`s.

```
stmap (f : A -> B) : (t : StreamTree A) -> StreamTree B
& v  => f t.v
& ts => smap t.ts

and

smap (f : A -> B) : (s : StreamOfStreamTree A) -> StreamOfStreamTree B
& hd => stmap s.hd
& tl => smap s.tl
```

We can now define `stmap` and `smap` by mutual corecursion. The code is identical to what we have seen in the previous section.

```
codata CoRoseTree (A : Type) : Type
| Empty
| Node of (v : A, ts : CoListOfCoRoseTree)

and

codata CoListOfCoRoseTree (A : Type) : Type
| Nil
| Cons of (hd : CoRoseTree, tl : CoListOfCoRoseTree)
```

Similarly, we mutually define the type of `CoRoseTree`s together and `CoListOfCoRoseTree`, which is just `CoList` specialized to `CoRoseTree`.

```
crmap (f : A -> B) : CoRoseTree A -> CoRoseTree B
| Empty    => Empty
| Node v l => Node (f v) (clmap l)

and

clmap (f : A -> B) : CoListOfCoRoseTree A -> CoListOfCoRoseTree B
| Nil      => Nil
| Cons h t => Cons (crmap h) (clmap t)
```

The code for `crmap` and `clmap` again is exactly identical to what we have seen previously.

```
codata CoListTree (A : Type) : Type
& v  of A
& ts of CoListOfCoListTree

and

codata CoListOfCoListTree (A : Type) : Type
| Nil
| Cons of (hd : CoListTree, tl : CoListOfCoListTree)
```

Mutual Coinductive Types need not both be negative or both be positive - they can also be mixed, i.e. some may be negative while others are positive. An example of such types is shown above. We define `CoListTree`, which is a necessarily infinite tree that has a value of type `A` at the root and a potentially infinite sequence of subtrees, which is represented as `CoListOfCoListTree`, the type of `CoList`s specialized to `CoListTree`. Both types are defined simultaneously.

```
cltmap (f : A -> B) : (t : CoListTree A) -> CoListTree B
& v  => f t.v
& ts => clomap t.ts

and

clomap (f : A -> B) : CoListOfCoListTree A -> CoListOfCoListTree B
| Nil      => Nil
| Cons t ts => Cons (cltmap t) (clomap ts)
```

We can define functions for map over these types by mutual corecursion. `cltmap`, which works on `CoListTree`s, applies `f` to the value stored at the root and calls `clomap`, which deals with mapping over `CoListOfCoListTree`. This latter function, when it deals with the `Cons` case, uses `cltmap` to map over the tree `t` and corecursively calls itself to deal with `ts`, the rest of subtrees.

```
mutual
  (A : Type)

  codata CoListTree : Type
  & v  of A
  & ts of CoListOfCoListTree

  codata CoListOfCoListTree : Type
  | Nil
  | Cons of (hd : CoListTree, tl : CoListOfCoListTree)

mutual
  #(A B : Type) (f : A -> B)

  cltmap : (t : CoListTree A) -> CoListTree B
  & v  => f t.v
  & ts => clomap t.ts

  clomap : CoListOfCoListTree A -> CoListOfCoListTree B
  | Nil      => Nil
  | Cons t ts => Cons (cltmap t) (clomap ts)
```

As for mutual inductive types, we can put mutual coinductive/corecursive definitions into `mutual` blocks which allow us to specify parameters shared across definitions. The above snippet shows how the definitions of `CoListTree`, `CoListOfCoListTree`, `cltmap` and `clomap` look in this syntax. Also similarly to mutual inductives, we may optionally provide a name for the whole `mutual` block and/or end it with the `end` keyword.

Are Mutually Coinductive Types good for anything besides encoding Nested Coinductive Types? As of now probably not, but they become a lot more useful once we have Coinductive Families at our disposal...

Papers:
- Take a look at the papers mentioned in the section on [Mutual Inductive Types](#mutual-inductive-types)

**Status: Mutual Coinductive Types are supported by Coq (and probably also by Agda, but I need to check), so they shouldn't be problematic. However, other proof assistants like Lean or Idris I think, don't directly support Mutual Coinductive Types or coinductive types at all for that matter.**

TODO:
- Search for papers.
- Learn which languages (Agda?) support Mutual Coinductive Types.
- Learn what's up with the criterion that each coinductive type in a mutual definition must have the same parameters. Coq has this and it's sometimes annoying.

### Coinductive Families <a id="coinductive-families"> [↩](#toc)

Coinductive Families are the dual of Inductive Families. Syntactically, we need to explicitly specify the domain of each field, just as we need to explicitly specify codomains when defining inductive families. The domain is the family being defined applied to some indices. The variables used in the indices need not be explicitly universally quantified, because we know that they must be anyway.

```
codata Odd : CoNat -> Prop
& Oz  : Odd z -> Empty
& Oss : (#n : CoNat) -> Odd (s (s n)) -> Odd n
```

The above example defines a predicate `Odd` on conatural numbers. `Odd` has two fields, `Oz` and `Oss`, but not all proofs of `Odd c` can access these fields. The type of `Oz` is `Odd z -> Empty`, so this field can only be accessed if we have `x : Odd z`, i.e. a proof that zero is `Odd`. The other field, `Oss`, is of type `(#n : CoNat) -> Odd (s (s n)) -> Odd c`, so it can only be accessed by proofs of `Odd` for conaturals greater than or equal to two.

```
zero-not-Odd (x : Odd z) : Empty :=
  x.Oz
```

We begin by showing that zero is not `Odd`. This is easy - we can fetch the proof of `Empty` directly from the field `Oz`.

```
Odd-one : Odd (s z)
& Oz impossible
& Oss impossible
```

Next up, one is `Odd`. To prove this, we need to provide definitions for the two fields `Oz` and `Oss`. But the index of `Oz` is `z`, whereas our proof has index `s z`, so we don't need to define this field - it is `impossible` to apply `Oz` to `Odd-one : Odd (s z)`. Similarly, the `Oss` field also doesn't need to be defined, because its index is `s (s n)` for some `n`, but the index of `Odd-one` is `s z`. This is dependent copattern matching in action!

```
Odd-one' : Odd (s z)
& impossible
```

Of course writing `impossible` for every field gets boring pretty fast, so we can use the special copattern `& impossible` to mark the fact that none of fields needs to be defined.

```
Odd-one'' : Odd (s z)
```

Another possibility, more experimental, is to just leave `Odd-one''` without any definition at all. Since no fields need to be defined, this is a valid definition and not just a declaration of an axiom.

```
two-not-Odd (x : Odd (s (s z))) : Empty :=
  x.Oss.Oz
```

We now prove that two is not `Odd`. This is easy - we need to grab the fact that zero is `Odd` using the field `Oss` and then we need to derive the contradiction from that using the field `Oz`.

```
Odd-three : Odd (s (s (s z)))
& Oz impossible
& Oss
  & Oz impossible
  & Oss impossible
```

Next, three is `Odd`. That's pretty easy - the field `Oz` is `impossible`, and we define the field `Oss` to be... well, its own `Oz` field is `impossible` and so is its `Oss` field.

```
Odd-three' : Odd (s (s (s z)))
& Oz impossible
& Oss => Odd-one
```

Alternatively, we can define its `Oss` field to be `Odd-one`.

```
Odd-three'' : Odd (s (s (s z)))
& Oss => Odd-one
```

We also don't need to write the `impossible` cases, so we can do this with a one-liner.

```
omega : CoNat := s omega

Odd-omega : Odd omega
& Oss => Odd-omega
```

Now, a proof that `omega`, the infinite number, is `Odd`. That's easy - `Oz` is `impossible` and `Oss` gets taken care of by a corecursive call.

This is the end of the example, but the last word about Coinductive Families has not yet been spoken! This is because so far we have only seen negative Coinductive Families, but Coinductive Families need not be negative - they can also be positive! In such a case, the syntax is the same as for inductive families.

```
codata Odd : CoNat -> Prop
| Osz : Odd (s z)
| Oss : (#n : CoNat) -> Odd n -> Odd (s (s n))
```

The above example shows how to define the predicate `Odd` as a positive coinductive family. Let's prove all the above theorems again with this new positive definition.

```
zero-not-Odd : Odd z -> Empty
| Osz impossible
| Oss impossible
```

Zero is not `Odd`, because when matching on a supposed proof of `Odd z`, neither the constructor `Osz` nor `Oss` has the right index - both are `impossible`.

```
zero-not-Odd' : Odd z -> Empty
| impossible
```

We can make this proof shorter by saying that no cases are possible, using the pattern `| impossible` that we have already met when discussing Inductive Families.

```
zero-not-Odd'' : Odd z -> Empty
```

An even shorter possibility is to just write no clauses at all. This is not interpreted as a declaration of an axiom, but rather as a definition - no clauses are possible, so none need to be provided.

```
Odd-one : Odd (s z) :=
  Osz
```

Next, one is `Odd`. This "theorem" is exactly the constructor `Osz`.

```
two-not-Odd : Odd (s (s z)) -> Empty
| Osz impossible
| Oss e with e
  | Osz impossible
  | Oss impossible
```

We now prove that two is not `Odd`, which requires quite some writing. First, the `Osz` constructor is `impossible` because the index doesn't match. The second possibility is that our proof of `Odd (s (s z))` was constructed from `Oss e` where `e : Odd z`. But when we match on `e` using a `with`-clause, we get two more `impossible` clauses whose constructor index doesn't match.

```
two-not-Odd' : Odd (s (s z)) -> Empty
| Oss e => zero-not-Odd e
```

An alternative way to prove this fact is to skip the first `impossible` case (as in general we don't need to handle `impossible` cases) and then use the already proven fact that zero is not `Odd` in the `Oss` case.

```
Odd-three : Odd (s (s (s z))) :=
  Oss Osz
```

Proving that three is `Odd` is again very easy - first we use the constructor for the `s (s n)` case and then the one for the `s z` case.

```
omega : CoNat := s omega

Odd-omega : Odd omega :=
  Oss Odd-omega
```

Proving that `omega` is `Odd` is just as easy as with the negative definition.

In general, the duality between the negative and the positive definition is crystal clear. For the negative definition, the "contradictory" theorems for even numbers are easy - we just need to project the contradiction out of the purported proof - whereas the true theorems for odd numbers require somewhat more work, as we need to mark all the `impossible` cases. For the positive definition, on the other hand, the true odd cases are easily provable by direct use of constructors, whereas the "contradictory" even cases require more work to mark all the `impossible` cases.

Which of these two definitions is better? Are they even equivalent? Let's find out (in the code that follows, we refer to the negative `Odd` as `NOdd` and to the positive `Odd` as `POdd`).

```
f : (n : CoNat, x : NOdd n) -> POdd n
| z      , _ => abort x.Os
| s z    , _ => Osz
| s (s n), _ => Oss (f n x.Oss)

g : (#n : CoNat, x : POdd n) -> NOdd n
| Osz => Odd-one
| Oss x'
  & Oz impossible
  & Oss => g x'
```

As we can see, the negative and positive definitions of `Odd` are logically equivalent (and thus, by univalence, equal, because they are both propositions). But the question of which is better remains.

In short: the `CoNat`ural numbers are a positive coinductive type and when we think about the usual `Nat`ural numbers being even or odd, we also prefer the inductive, i.e. positive, definition. Moreover, the positive definition seems very natural (it tells us which numbers are `Odd`; pun intended), whereas the negative definition seems very odd (it basically tells us which numbers are not even, and thus odd; pun intended). Therefore, the positive definition of `Odd` is better. However, for other predicates or type families, negative definitions may turn out to be better.

Last but not least, it would be nice to know how the syntax for positive coinductive families desugars. Below we define the family of "covectors", which are like vectors but possibly infinite and indexed by conaturals instead of naturals.

```
codata CoVec (A : Type) : CoNat -> Type
| CoNil  : CoVec z
| CoCons : (hd : A, #c : CoNat, tl : CoVec c) -> CoVec (s c)
```

The whole thing desugars as follows.

```
data CoVecF (A : Type) (F : CoNat -> Type) : CoNat -> Type
| CoNilF  : CoVecF z
| CoConsF : (h : A, #c : CoNat, t : F c) -> CoVecF (s c)
```

First, we define `CoVecF`, the base functor of `CoVec`, defined inductively. It is like `CoVec` but with self-references replaced with arguments of type `F c` which is a parameter.

```
codata CoVec (A : Type) : (c : CoNat) -> Type
& out of CoVecF A CoVec c
```

Then we coinductively "tie the knot" of the base functor to get the desired family `CoVec`.

```
CoNil (#A : Type) : CoVec A z
& out => CoNilF

CoCons (h : A) (#c : CoNat) (t : CoVec A c) : CoVec A (s c)
& out => CoConsF h t
```

Finally, the constructors of `CoVec` are just wrappers around the constructors of `CoVec`.

Papers:
- [Elaborating dependent (co)pattern matching](https://jesper.sikanda.be/files/elaborating-dependent-copattern-matching.pdf)

**Status: coinductive families need to be encoded using equality fields written by hand in Coq. I'm not sure about Agda, though. Implementing coinductive families as presented here probably wouldn't pose much of a problem.**

TODO:
- Polish the writing.
- Search for more papers.
- Figure out the final notation: `of` as a short-hand when defining inductive and coinductive types and the colon `:` when defining families?

### Nested Coinductive Families <a id="nested-coinductive-families"></a> [↩](#toc)

Nested Conductive Families are the dual of Nested Inductive Families, i.e. they are coinductive families `C` in which the coinductive occurrence of `C` in the indices is nested in some type constructor.

```
codata Complete : Type -> Type
| E : (#A : Type) -> Complete A
| N : (#A : Type, v : A, ts : Complete (A * A)) -> Complete A
```

The simplest example is a coinductive version of the `Complete` binary trees we have seen when discussing Nested Inductive Families. The only difference is that now our complete trees can potentially be infinite.

```
cmap : (#A #B : Type, f : A -> B, t : Complete A) -> Complete B
| _, E      => E
| _, N v ts => N (f v) (cmap (fun (x, y) => (f x, f y)) ts)
```

Let's define a mapping function, as usual. Just as for NIFs, we now need to treat `A`, `B` and `f` as indices and not parameters. In the corecursive call to `cmap`, we need to lift `f` to a function `A * A -> B * B`, which we do inline. There isn't much difference from the inductive version. In fact, the code is exactly the same.

```
codata Complete' : Type -> Type
& v  : (#A : Type) -> Complete' A -> A
& ts : (#A : Type) -> Complete' A -> Complete' (A * A)
```

Nested Coinductive Families can be negative too. Above, we see a variant of `Complete` for which all binary trees are necessarily infinite.

```
cmap' : (#A #B : Type, f : A -> B, t : Complete' A) -> Complete' B
& v  => f t.v
& ts => cmap' (fun (x, y) => (f x, f y)) t.ts
```

To define `cmap'`, we need the same trick as for positive nested types - we need to lift `f : A -> B` to a function `A * A -> B * B`.

But just as in the inductive case, the above examples are just the tip of the iceberg.

```
codata Obama : Type -> Type
& hd : (#A : Type) -> Obama A -> A
& tl : (#A : Type) -> Obama A -> Obama (Obama A)
```

The most obvious example of a truly nested coinductive family is shown above. The field names `hd` and `tl` were used because this type is quite similar to `Stream`, just more nested.

Note: we call this type `Obama`, because it is to nested coinductive families what `Bush` is to nested inductive families. I hope you can see the pun...

```
omap : (#A #B : Type, f : A -> B, s : Obama A) -> Obama B
& hd => f s.hd
& tl => omap (omap f) s.tl
```

To define the mapping function for `Obama`s, for the `tl` field we need to use the scary self-referring higher-order corecursive call `omap (omap f) s.tl`. Something like it is supported absolutely nowhere, except in our language of course... or so I wish.

```
codata CoBush : Type -> Type
| Nil  : (#A : Type) -> CoBush A
| Cons : (#A : Type, hd : A, tl : CoBush (CoBush A)) -> CoBush A
```

We also have truly nested positive coinductive families. The simplest among them is `CoBush`, the coinductive version of `Bush` that we have seen previously.

```
bmap : (#A #B : Type, f : A -> B, b : CoBush A) -> CoBush B
| Nil      => Nil
| Cons h t => Cons (f h) (bmap (bmap f) t)
```

Defining `bmap` for `CoBush` is as easy (or as hard, depending on how you look at it) as defining it for `Bush`. Yet again, we need to use a scary higher-order corecursive call, `bmap (bmap f)`.

Papers:
- None

**Status: extremely speculative.**

TODO:
- Search for papers.
- Write some code dealing with truly nested coinductive families.
- Decide if the last piece of syntax sugar should be included.
- Change syntax of basic (co)inductives to use `of`.

### Syntax sugar for coinductive families with uniform indices <a id="coinductive-uniform-indices"></a> [↩](#toc)

Coinductive Families enjoy an analogous kind of syntax sugar to what we have seen for Inductive Families. For negative coinductive types, if domains of all fields have the same indices (i.e. they have _uniform indices_), we don't need to quantify the domain indices in every field separately - we can use the `of` syntax used for ordinary negative coinductive types, which omits the domain. For positive coinductive types, this syntax sugar works exactly the same as for inductive types.

This syntax sugar is most useful for nested coinductive families, as they are the most common example of coinductive families with uniform indices.

Let's see how the examples from [the previous section](#nested-coinductive-families) look like when translated to this new syntax sugar.

```
codata Complete : (A : Type) -> Type
| E
| N of (v : A, ts : Complete (A * A))

codata Complete' : (A : Type) -> Type
& v  of A
& ts of Complete' (A * A)

codata Obama : (A : Type) -> Type
& hd of A
& tl of Obama (Obama A)

codata CoBush : (A : Type) -> Type
| Nil
| Cons of (hd : A, tl : CoBush (CoBush A))
```

As you can see, we now need to name the index to be able to refer to it, because it is not quantified. For negative types, field types are given after `of` and we omit the domain, whereas for positive types the constructor arguments are given after `of` and we omit the codomain. Contrary to ordinary coinductive types, we need to explicitly state what the index is for coinductive arguments. In the end, the new syntax sugar saves us from quite some typing, especially for longer definitions.

For papers, status and TODOs, see [the analogous section for inductive types](#inductive-uniform-indices).

### A more verbose (and readable) syntax for coinductive types <a id="verbose-syntax-for-coinductives"></a> [↩](#toc)

Just as for inductive types, for coinductive types too we have a more verbose, but also more readable, special syntax.

```
codata Stream
  parameters
  & A : Type
  sort Type
  constructor Cons
  fields
  & hd of A
  & tl of Stream
```

For negative coinductive types, this syntax is very similar to that for inductive types. We start with the keyword `parameters`, below which we list the type's parameters in copattern syntax, then the keyword `sort`, followed by the type's universe, then we can optionally specify an alias for the type's constructor, after the keyword `constructor`. Finally, we have the keyword `fields` followed by the type's fields in copattern syntax.

```
mutual
  parameters
  & A : Type

  codata StreamTree : Type
  & v  of A
  & ts of StreamOfStreamTree

  codata StreamOfStreamTree : Type
  & hd of StreamTree
  & tl of StreamOfStreamTree

mutual
  parameters
  & A B : Type
  & f : A -> B

  mapst : (t : StreamTree A) -> StreamTree B
  & v  => f t.v
  & ts => maps t.ts

  maps : (s : StreamOfStreamTree A) -> StreamOfStreamTree B
  & hd => mapst s.hd
  & tl => maps s.tl
```

Just as was the case for mutual inductive types, we have a special verbose version of `mutual` blocks, in which we can specify parameters in copattern syntax following the `parameters` keyword and these are shared across all definition in the block. Verbose `mutual` blocks work for both coinductive type definitions and corecursive function definitions.

```
codata Odd
  indices
  & n : CoNat
  sort Prop
  constructor MkOdd
  fields
  & Oz  : Odd z -> Empty
  & Oss : (#n : CoNat) -> Odd (s (s n)) -> Odd n
```

The verbose syntax also works for coinductive families, with the keyword `indices` being used to specify the indices.

The verbose syntax for positive coinductive types is almost the same as for inductive types, with the exception that we can't specify an alias for the elimination rule (because positive coinductive don't have an elimination rule of the same kind as inductive types).

Papers:
- None, this is my idea.

**Status: if the verbose syntax works for inductive types, then surely it also does for coinductive types. So, it shouldn't pose any problems.**

TODO:
- Change the keyword `fields` to `destructors`?
- Change the keyword `constructor` to `introductor`?

### [Coinduction-Coinduction](Coinduction/Coinduction-Coinduction) <a id="coinduction-coinduction"></a> [↩](#toc)

In one of the previous sections we have seen induction-induction, which is a mechanism for simultaneously defining an inductive type and an inductive family indexed by this type. What about "coinduction-coinduction" or something like that, which would be the dual thing in the world of coinduction? Is it possible?

#### Negative Coinduction-Coinduction, with the family not really being coinductive

Let's find out by defining binary heaps again.

```
codata BHeap (R : A -> A -> Prop) : Type
& root of A
& l    of BHeap
& r    of BHeap
& okl  of OK R root l
& okr  of OK R root r

and

codata OK (R : A -> A -> Prop) : (root : A, h : BHeap) -> Prop
& ok of R root h.root
```

The above snippet defines a type `BHeap R` of necessarily infinite binary heaps. The heaps are trees that have a `root` and two subtrees, `l` and `r`, that satisfy the heap property. The property is called `OK` and is defined together with `BHeap`. It is defined using the `codata` keyword, but in fact is not very coinductive, as it is just wraps a proof of `R root h.root`, where `root` will be filled by the root of the binary heap and `h.root` will be filled by the root of the left or right subtree of the heap.

```
map
  #(A B : Type)
  (R : A -> A -> Prop) (S : B -> B -> Prop)
  (f : A -> B)
  (pres : #(x y : A) -> R x y -> S (f x) (f y))
  : (h : BHeap R) -> BHeap S
& root => f h.root
& l    => map h.l
& r    => map h.r
& okl  => map-ok h.okl
& okr  => map-ok h.okr

and

map-ok
  #(A B : Type)
  (R : A -> A -> Prop) (S : B -> B -> Prop)
  (f : A -> B)
  (pres : #(x y : A) -> R x y -> S (f x) (f y))
  : (#v : A, #h : BHeap R, p : OK R v h) -> OK S (f v) (map h)
& ok => pres p.ok
```

We can define functions on the type `BHeap` in the usual way. Above, we define a mapping function `map : BHeap R -> BHeap S`, which transforms `R`-ordered heaps into `S`-ordered heaps, provided that the argument function `f` maps `R`-related inputs to `S`-related outputs (the proof of this fact is called `pres` and is an argument).

The definition goes by copattern matching. The definitions for the fields `root`, `l` and `r` are quite obvious. For the fields `okl` and `okr`, we need to use `pres`, but we cannot do this directly - we need to prove a lemma `map-ok`, which establishes that `map` preserves the heap property (or rather, transforms the `R`-heap property into the `S`-heap property). This lemma is defined/proved mutually with `map` - this is our old good mutual corecursion (even though `map-ok` is not really corecursive).

It is not hard to see that the definition is somewhat lengthy and complicated, even though defining `map` should be simple - as simple as for ordinary (co)inductive types and families. We could try to make it shorter using a `mutual` block or a similar trick, but it wouldn't help much. To make the definition of `BHeap` really pleasant, we need more syntax sugar!

```
codata BHeap (R : A -> A -> Prop) : Type
& root of A
& l    of BHeap
& r    of BHeap
& okl  of R root l.root
& okr  of R root r.root
```

This syntax sugar is shown above. The crux is that in coinductive-coinductive definitions, if the family is a not really coinductive wrapper for a record, we can inline it - above, `okl` and `okr` are no longer of type `OK ...`, but become mere proofs that establish the heap property.

```
map
  #(A B : Type) (R : A -> A -> Prop) (S : B -> B -> Prop)
  (f : A -> B) (pres : #(x y : A) -> R x y -> S (f x) (f y))
  : (h : BHeap R) -> BHeap S
& root => f h.root
& l    => map h.l
& r    => map h.r
& okl  => pres h.okl
& okr  => pres h.okr
```

Using this syntax sugar, the definition of `map` is much simpler, as we no longer need to resort to mutual corecursion.

```
codata BST (R : A -> A -> Prop) : Type
constructor N
& root of A
& l    of BST
& r    of BST
& okl  of R l.root root
& okr  of R r.root root -> Empty
```

Using our syntax sugar, it is similarly easy to define a type of necessarily infinite binary search trees (modulo the usual difficulties with the order relation). If you want to learn more about these two types, see the files [Coind/Coinduction-Coinduction/NegativeBHeap.ttw](NegativeBHeap.ttw) and [Coind/Coinduction-Coinduction/NegativeBST.ttw](NegativeBST.ttw). For a simpler data structure, take a look at [sorted streams](Coinduction/Coinduction-Coinduction/SortedStream.ttw).

#### Positive Coinduction-Coinduction, with the family not really being coinductive

We can also have positive coinductive-coinductive types. Let's see how this works by defining binary heaps yet again, but this time they will be only possibly infinite.

```
codata BHeap (R : A -> A -> Prop) : Type
| E
| N of (root : A, l r : BHeap, okl : OK R root l, okr : OK R root r)

and

codata OK (R : A -> A -> Prop) : A -> BHeap -> Prop
| OK-E : #(root : A) -> OK root E
| OK-N : #(root x : A) #(l r : BHeap R) (okl : OK x l) (okr : OK x r) (p : R root x) -> OK root (N x l r okl okr)
```

This time, our heaps are either `E`mpty or a `N`ode with a value at the `root` and with two subtrees, together with proofs establishing that the node satisfies the heap property.

```
map
  #(A B : Type)
  (R : A -> A -> Prop) (S : B -> B -> Prop)
  (f : A -> B)
  (pres : #(x y : A) -> R x y -> S (f x) (f y))
  : (h : BHeap R) -> BHeap S
| E => E
| N => N
  & root => f h.root
  & l    => map h.l
  & r    => map h.r
  & okl  => map-ok h.okl
  & okr  => map-ok h.okr

and

map-ok
  #(A B : Type)
  (R : A -> A -> Prop) (S : B -> B -> Prop)
  (f : A -> B)
  (pres : #(x y : A) -> R x y -> S (f x) (f y))
  : (#root : A, #h : BHeap R, ok : OK R root h) -> OK S (f root) (map h)
| OK-E => OK-E
| OK-N => OK-N
  & okl => map-ok ok.okl
  & okr => map-ok ok.okr
  & p   => pres ok.p
```

The definition of `map` for our positive `BHeap`s is almost the same as for the negative `BHeap`s, i.e. rather bloated. The only difference is that now we need to also handle the `E` case, which is trivial.

Thaknfully, we can make use of the same syntax sugar that saved us from bloat in the negative case.

```
codata BHeap (R : A -> A -> Prop) : Type
| E
| N of
  & root of A
  & l r  of BHeap
  & okl  of l is N -> R root l.root
  & okr  of r is N -> R root r.root
```

Above, we have inlined `OK` into `okl` and `okr`, but there's a significant difference from what we have done for the negative case. Because our type is positive now, we can't just say `R root l.root`, because the left subtree `l` is not a record anymore - it might be `E`mpty (and like wise for `r`).

If we want to write `l.root`, we need to make sure that `l` is a `N`ode. To this effect, we use `l is N` as the premise of `R root l.root`. Because of how `is` works, to the right of `l is N` we know that `l` is convertible with `N root' l' r' okl' okr'` for some `root', l', r', okl'` and `okr'`, so that writing `l.root` (which is convertible with `root'`) is legal (if you don't remember, this is because we may refer to `l`s constructor's argument by writing `l.`).

```
map
  #(A B : Type)
  (R : A -> A -> Prop) (S : B -> B -> Prop)
  (f : A -> B)
  (pres : #(x y : A) -> R x y -> S (f x) (f y))
  : (h : BHeap R) -> BHeap S
| E => E
| N => N
  & root => f h.root
  & l    => map h.l
  & r    => map h.r
  & okl with h.l
    | E => fun e : map h.l is N => abort e
    | N => fun _ : map h.l is N => pres (h.okl (_ : h.l is N))
  & okr with h.r
    | E => fun e : map h.r is N => abort e
    | N => fun _ : map h.r is N => pres (h.okr (_ : h.r is N))
```

With our syntax sugar, the definition of `map` is significantly shorter (17 lines, down from 27, or a reduction of 37%), although it still looks a little scary. This is because we need a nested pattern match to handle `okl` and `okr`.

Let's consider `okl`, as `okr` is completely analogous. There are two cases: `E` and `N`. If `h.l` matches `E`, then we get a contradiction, because the premise of the `okl` field we need to define is `map h.l is N`, but this computes to `map E is N` and then to `E is N`, which is obviously false. We only need to use `abort` on `e`, the proof of `map h.l is N`. In the second case, when `h.l` matches `N`, we need to use `pres` on `h.okl` to which we feed a proof of `h.l is N`, automatically inferred during elaboration.

For code examples of positive coinduction-coinduction (without the syntax sugar), see [PositiveBHeap.ttw](Coinduction/Coinduction-Coinduction/PositiveBHeap.ttw) and [PositiveBST.ttw](Coinduction/Coinduction-Coinduction/PositiveBST.ttw). For code examples that use the syntax sugar, see [PositiveBHeap_withIs.ttw](Coinduction/Coinduction-Coinduction/PositiveBHeap_withIs.ttw) and [PositiveBST_withIs.ttw](Coinduction/Coinduction-Coinduction/PositiveBST_withIs.ttw). For a simpler data structure, take a look at [sorted colists](Coinduction/Coinduction-Coinduction/SortedCoList.ttw).

#### More complicated cases

TODO: deduplicated streams

Papers:
- None

**Status: very speculative.**

TODO:
- Write a new version of this section.
- Search for papers.
- Find a good example of coinduction-coinduction.

### Coinduction-Corecursion <a id="coinduction-corecursion"></a> [↩](#toc)

Let's try to use induction-recursion syntax together with the `codata` keyword and see what happens. For exploration purposes, we will try to define a type of infinite binary heaps.

```
codata BHeap (R : A -> A -> Prop) : Type
| E
| N of (v : A, l r : BHeap, okl : OK R v l, okr : OK R v r)

and

OK #(R : A -> A -> Prop) (v : A) : (h : BHeap R) -> Prop
| E => Unit
| N => R v h.v
```

Aaaaand that's it. The definition looks pretty correct - it's copy-pasted from the earlier inductive-recursive definition of binary heaps, so it probably represents some kind of binary heaps. The only difference is the use of the `codata` keyword. Let's see how to desugar this.

```
data BHeapX (X : Type) (R : A -> A -> Prop) : Type
| E
| N of (v : A, l r : X, okl : OKX v l, okr : OKX v r)

and

OKX (#X : Type, #R : A -> A -> Prop, v : A) : (h : BHeapX X R) -> Prop
| E => Unit
| N => R v h.v

codata BHeap (R : A -> A -> Type) : Type
& Out of BHeapX BHeap R

OK #(R : A -> A -> Prop) (v : A) : (h : BHeap R) -> Prop :=
  OKX v h.Out
```

TODO: THE DESUGARING IS ILL-TYPED!

The desugaring is pretty self-explanatory. We define `BHeapX` and `OKX` by induction-recursion and then tie the knot by defining `BHeap` coinductively as the fixpoint of `BHeap` and `OK` as a wrapper around `OKX`.

The limits of positive coinduction-recursion seem to be pretty clear: we can mutually define dependent types coinductively and **non-recursive** functions by pattern matching. Recursive functions, however, are not allowed, because the inductive part of our desugaring is non-recursive, i.e. it is only one layer deep. Therefore, recursion is illegal in this case. This shouldn't be surprising - after all, defining recursive function by pattern matching on a coinductive argument is very illegal.

To sum up: there's no coinduction-recursion, but we can mutually define types coinductively and functions by pattern matching.

Papers:
- [Wander types: A formalization of coinduction-recursion](https://www.nii.ac.jp/pi/n10/10_47.pdf)

**Status: very speculative.**

TODO:
- Search for papers.
- Find a good example of coinduction-corecursion.

## Mixed Inductive and Coinductive Types <a id="mixed-inductive-coinductive"></a> [↩](#toc)

In most functional languages and proof assistants the inductive and coinductive worlds are either strictly separated, or, alternatively, the coinductive world is just missing (or, in Haskell, the inductive and coinductive worlds are the same thing). In OO, hybrid and dynamic languages the things are more shady.

In this section, we want to explain (and explore) a more principled approach to mixing inductive and coinductive types. We will see three main ideas:
- inductive types with global fields, i.e. fields that are present no matter which constructor was used to create the value
- coinduction-induction, i.e. a mechanism similar to induction-induction or coinduction-coinduction, but which allows to simultaneously define an inductive type and a coinductive predicate indexed by it, or a coinductive type and an inductive predicate indexed by it
- mixed inductive-coinductive types, i.e. types in which some occurrences of the self-referring argument may be inductive, while other occurrences may be coinductive

### Mixing records and sums: A * (B + C) = (A * B) + (A * C)<a id="mixing-records-and-sums"></a> [↩](#toc)

It may sometimes happen that all constructors of an inductive type share an argument and we want to avoid writing it over and over again. Or we may want to put some additional (co)data into values of an inductive type, but not into the type itself, so that it doesn't appear at the type level.

We introduce new syntax sugar which serves exactly this purpose. Consider the type below.

```
data ProdSum (A B C : Type) : Type
& a of A
| b of B
| c of C
```

`ProdSum` is a family of inductive types with three parameters, `A B C : Type`. It has two constructors, `b : B -> ProdSum A B C` and `c : C -> ProdSum A B C`, and one field `a : ProdSum A B C -> A`.

If we denote product as `*` and sum as `+`, then `ProdSum A B C` can be interpreted as `(A * B) + (A * C)`, i.e. a type that is made of either a `B` or a `C`, but also has a field of type `A`, no matter which constructor it was made with.

```
ab : ProdSum Bool Nat String :=
  b tt 0

ac : ProdSum Bool Nat String :=
  c ff "42"
```

To create values of type `ProdSum A B C`, we use the constructors, just like for ordinary inductive types, but we also need to specify the value of the field `a` - it is the first argument of both `b` and `c`.

```
ab' : ProdSum Bool Nat String :=
  b (a => tt, b => 0)

ac' : ProdSum Bool Nat String :=
  c (a => ff, c => "42")

ab'' : ProdSum Bool Nat String := b
& a => tt
& b => 0

ac'' : ProdSum Bool Nat String := c
& a => ff
& c => "42"
```

Of course we don't need to apply the arguments positionally - we can also use the tuple syntax or the copattern syntax. Note that the unnamed argument of `b` is in fact called `b`, just like the constructor itself, and analogously for `c`.

```
ab-a : ab.a = tt := refl
ac-a : ac.a = ff := refl
```

Given a value `x` of type `ProdSum A B C`, we can access the field `a` using the dot syntax, by writing `x.a`.

```
ab''' : ProdSum Bool Nat String
& a => tt
& __sum => b 0

ac''' : ProdSum Bool Nat String
& a => ff
& __sum => c "42"
```

Another way to think of the type `ProdSum A B C` is to treat it not as a sum, but as a product, i.e. as `A * (B + C)`. We can use the copattern syntax to define values of `ProdSum A B C`. In such a situation, the record-like part (i.e. all the fields) behaves like an ordinary record, whereas the sum-like part (i.e. the thing we build using constructors) behaves like an additional field of this record (this field is named `__sum`).

```
ad : ProdSum Bool Nat String :=
  (_ => ab, a => negb ab.a)

ad' : ProdSum Bool Nat String
& _ => ab
& a $=> negb
```

When working with `ProdSum A B C` using the tuple syntax or copattern syntax, we can also make use of prototyping and record update syntax.

```
data ProdSum' (A B C : Type) : Type
| b' of (a : A, b : B)
| c' of (a : A, c : C)

f : (x : ProdSum A B C) -> ProdSum' A B C
| b => b'
  & a => x.a
  & b => x.b
| c => c'
  & a => x.a
  & c => x.c

g : (x : ProdSum' A B C) -> ProdSum A B C
| b' => b
  & a => x.a
  & b => x.b
| c' => c
  & a => x.a
  & c => x.c

fg : (x : ProdSum A B C) -> g (f x) = x
| b => refl
| c => refl

gf : (x : ProdSum' A B C) -> f (g x) = x
| b' => refl
| c' => refl
```

Besides accessing the field `a`, we may also eliminate values of type `ProdSum A B C` like those of ordinary sums and inductive types, i.e. by pattern matching and recursion.

The above code shows `ProdSum'`, one of the possible desugarings of `ProdSum` (the one that corresponds to `(A * B) + (A * C)`). The two types are equivalent (and thus equal), which is showcased by functions `f` and `g`, which look almost identical (except for the `'`s).

```
data ProdSumAux (B C : Type) : Type
| b'' of (b : B)
| c'' of (c : C)

data ProdSum'' (A B C : Type) : Type
& a of A
& __sum' of ProdsumAux B C

f : (x : ProdSum A B C) -> ProdSum'' A B C
& a => x.a
& __sum' with x
  | b => b'' x.b
  | c => c'' x.c

g : (x : ProdSum'' A B C) -> ProdSum A B C :=
match x.__sum' with
| b'' bb => b x.a bb
| c'' cc => c x.a cc

fg : (x : ProdSum A B C) -> g (f x) = x
| b => refl
| c => refl

gf : (x : ProdSum'' A B C) -> f (g x) = x :=
match x.__sum' with
| b'' bb => refl
| c'' cc => refl
```

The above code shows `ProdSum''`, another of the possible desugarings of `ProdSum` (the one that corresponds to `A * (B + C)`). The two types are equivalent (and thus equal), which is showcased by functions `f` and `g`. This time the definitions are much more awkward, which shows that using `ProdSum''` instead of `ProdSum` would be pretty annoying.

```
data ProdProdSum (A B C D : Type) : Type
& a of A
& b of B
| c of C
| d of D
```

Of course, these mixed record-inductives may have more than one field. For example, the above type `ProdProdSum A B C D` has two fields, `a` of type `A` and `b` of type `B`. Intuitively, this type corresponds to `(A * B * C) + (A * B * D)`, or, equivalently, to `A * B * (C + D)`

```
data SumProdProd (A B C D : Type) : Type
| a of A
| b of B
& c of C
& d of D
```

Another possibly useful feature is to be able to put these shared constructor arguments at the end of the constructor's argument list. This is achieved by the above type `SumProdProd A B C D`, which intuitively corresponds to `(A * C * D) + (B * C  * D)`, or, equivalently, to `(A + B) * C * D`.

```
data ProdSumProd (A B C D : Type) : Type
& a of A
| b of B
| c of C
& d of D
```

Of course, we can put shared constructor arguments both at the beginning and at the end. This is shown above with the type `ProdSumProd A B C D`, which intuitively corresponds to `(A * B * D) + (A * C * D)`, or, equivalently, to `A * (B + C) * D`.

```
data Nel (A : Type) : Type
& hd of A
| Singl
| Cons of (tl : Nel)

codata CoNel (A : Type) : Type
& hd of A
| Singl
| Cons of (tl : CoNel)
```

We can also use mixed record-sums for defining inductive and coinductive types. Above we see the two most obvious examples: non-empty lists `Nel` and non-empty colists `CoNel`.

`Nel A` is a type whose values have a head `hd` and are either a `Singl`eton, which takes no arguments (besides the `hd`, of course), or a `Cons`, which takes the tail `tl` as an argument (in addition to `hd`, of course). `CoNel`, the type of non-empty colists, is analogous to `Nel`, of course with the twist that it is coinductive instead of inductive.

```
data ProdProdSum
  parameters
  & A B C D : Type
  sort Type
  fields
  & a of A
  & b of B
  constructors
  | c of C
  | d of D

data SumProdProd
  parameters
  & A B C D : Type
  sort Type
  constructors
  | a of A
  | b of B
  fields
  & c of C
  & d of D

data ProdSumProd
  parameters
  & A B C D : Type
  sort Type
  fields
  & a of A
  constructors
  | b of B
  | c of C
  fields
  & d of D
```

Besides the standard syntax, we can also define mixed record-sums using verbose syntax that we have seen before for inductive and coinductive types. Using this syntax, we can add some shared constructor arguments below the `fields` keyword. If the `fields` keyword precedes the `constructors` keyword, then these shared constructor arguments are placed at the front of the constructors. If `fields` follows `constructors`, they are placed at the end. If `fields` appears both before and after `constructors`, some shared constructor arguments are placed at the front and others at the end.

Last but not least, it would be good to know where we can use this weird feature (try to think of a single language that has it!). A general answer is that mixed record-sums are useful every time we needto attach some metadata to a sum or an inductive type. A more specific one would be parsers - these usually are sums (many possible productions), but also need to store metadata about number line, column and possibly much more.

Papers:
- None

**Status: this is my own idea, but it seems very easy to implement.**

TODO:
- Try to find some papers (or any writing on the topic, for that matter).

### Coinduction-Induction? Somewhat. <a id="coinduction-induction"></a> [↩](#toc)

The classical example of a mixed coinductive-inductive type is the type of stream processors `SP A B`. It is a more concrete (even though still higher-order) representation of functions of type `Stream A -> Stream B`. The main purpose of it is to define stream processing functions which might not be accepted by the productivity checker.

```
mutual
  parameters
  & A B : Type

  codata SP : Type
  | Put of (hd : B, tl : SP)
  | Get of (gsp : A -> GetSP)

  data GetSP : Type
  | Put of (hd : B, tl : SP)
  | Get of (g : A -> GetSP)
```

The implementation is somewhat mysterious, so let's go over it in detail.

The type `SP A B` is the type of stream processors. It is defined coinductively (using our positive coinductive syntax sugar), because it is supposed to represent the "output part" of a stream processing function. Since the output is a stream, and streams are coinductive, `SP A B` is also coinductive.

It has two constructors, `Put` and `Get`. `Put` should be interpreted as the function outputting a single element of the output stream (`hd : B`) and then there's the rest of the stream processors (`tl : SP A B`). `Get` is used when the function needs to see what's in the input stream before deciding on the output. Its argument `gsp` is of type `A -> GetSP A B`, which should be interpreted as "peek at the first element of the input stream and then maybe at some more, until you decide on the output".

The type `GetSP A B` is the "input part" of our stream processing. Since our stream processing function is supposed to be productive, it can only look up a finite prefix of the input stream before deciding on the output, so `GetSP A B` is an inductive type.

It has two constructors named `Put` and `Get`. `Put` should be interpreted as the function having checked enough inputs to produce an output (`hd : B`), and thus so we return to the output mode (`tl : SP A B`). `Get` should be interpreted as the function still having to see more elements of the input stream.

Ok, that's more or less it when it comes to the type itself. But since the type of stream processors was supposed to represent functions in the first place, let's see how to interpret `SP A B` as a function `Stream A -> Stream B`.

```
toStream : (f : SP A B) (s : Stream A) -> Stream B
& hd
  | Put => f.hd
  | Get => head (f.gsp s.hd) s.tl
& tl
  | Put => toStream f.tl s
  | Get => tail (f.gsp s.hd) s.tl

and

head : (g : GetSP A B) (s : Stream A) -> B
| Put => g.hd
| Get => head (g.g s.hd) s.tl

and

tail : (g : GetSP A B) (s : Stream A) -> Stream B
| Put => toStream g.tl s
| Get => tail (g.g s.hd) s.tl
```

Out first attempt consists of three mutually defined functions. The main function is `toStream`, defined corecursively, and the helper functions are `head` and `tail`, defined recursively. `toStream` works as follows. The `hd` of the result stream is extracted from the stream processor `f : SP A B` if it is a `Put` and otherwise we use the helper function `head` to compute it by feeding the input stream to `f.gsp`. As for the `tl`, we corecursively compute it from the tail of the stream processor if it is `Put` and in case it's `Get`, we use the helper function `tail` which computes it by feeding the input stream `s` to `f.gsp`.

We might be a little dissatisfied with our first attempt, however, because it looks somewhat redundant. Namely, the recursion scheme of `head` and `tail` are very similar, so maybe they could be merged?

```
%Corecursive
toStream : (f : SP A B) (s : Stream A) -> Stream B
| Put
  & hd => f.hd
  & tl => toStream f.tl s
| Get => toStream' (f.gsp s.hd) s.tl

and

toStream' : (g : GetSP A B) (s : Stream A) -> Stream B
| Put
  & hd => g.hd
  & tl => toStream g.tl s
| Get => toStream' (g.g s.hd) s.tl
```

The second attempt results in a much more compact definition. We use pattern matching at the top level to make the definition shorter, but `toStream` is still to be understood corecursively, thanks to the `%Corecursive` directive.

In the `Put` case, we unpack the head of the stream from the argument and compute the tail corecursively, just as in the first definition. In the `Get` case, we use `toStream'`, which computes the result stream recursively from `g : GetSP A B` and `s : Stream A`. In the `Put` case, it behaves the same as `toStream`, whereas in the `Get` case it recursively feeds the input stream `s` into `g`. As we can see, we managed to cut down the redundancy.

But we may still be somewhat dissatisfied, because `toStream` and `toStream'` are defined by mutual corecursion-recursion, which is a suspicious principle. Can we untie them so that we first define `toStream'` by recursion and only then `toStream` by corecursion? Let's try.

```
whnf : (g : GetSP A B) (s : Stream A) -> (hd : B, tl : SP A B, s : Stream A)
| Put => (g.hd, g.tl, s)
| Get => whnf (g.g s.hd) s.tl

toStream : (f : SP A B) (s : Stream A) -> Stream B
| Put
  & hd => f.hd
  & tl => toStream f.tl s
| Get =>
  let x := whnf (f.g s.hd) s.tl in
    & hd => x.hd
    & tl => toStream x.tl x.s
```

As we see, it is possible to avoid mutual corecursion-recursion. We attain this by getting rid of `toStream'` and instead defining a function called `whnf`, whose role is to feed an input stream `s` into `g : GetSP A B` in order to compute whatever is necessary for the `Get` case in `toStream`, i.e. the head of the stream, the rest of the stream processor and the remaining input stream. Our definition didn't get any shorter in the process, however. Also note that we can use `let` together with copatterns pretty seamlessly.

The last thing we should probably want to know is how does this desugar.

```
data SP' (X Y A B : Type) : Type
| Put' of (hd : B, tl : X)
| Get' of A -> Y

data GetSP' (X A B : Type) : Type
| In of SP' X GetSP' A B

codata SP (A B : Type) : Type
& Out of SP' SP (GetSP' SP A B) A B

GetSP (A B : Type) : Type :=
  GetSP' (SP A B) A B

Put #(A B : Type) (hd : B, tl : SP A B) : GetSP A B :=
  In (Put' hd tl)

Get #(A B : Type) (g : A -> GetSP A B) : GetSP A B :=
  In (Get' g)

// Some name clashes, but this shouldn't matter.
Put #(A B : Type) (hd : B, tl : SP A B) : SP A B :=
& Out => Put' hd tl

Get #(A B : Type) (gsp : A -> GetSP A B) : SP A B :=
& Out => Get' gsp

toStream : (f : SP A B) (s : Stream A) -> Stream B
& hd with Out f
  | Put' h _ => h
  | Get' gsp => hd (toStream' (gsp s.hd) s.tl)
& tl with Out f
  | Put' _ t => toStream t s
  | Get' gsp => tl (toStream' (gsp s.hd) s.tl)

and

toStream' : (g : GetSP A B) (s : Stream A) -> Stream B
| Put', _
  & hd => g.hd
  & tl => toStream g.tl s
| Get', _ => toStream' (g.g s.hd) s.tl
```

Since both `SP` and `GetSP` have the same base functor (or more poetically, the same "skeleton"), we don't need to duplicate it. Then we tie the knot twice, first inductively to obtain an early version of `GetSP` and then coinductively to obtain `SP`. Then we define the final version of `GetSP` and smart constructors that wrap the actual constructors in `In` and `Out`. The desugaring of `toStream` and `toStream'` is somewhat ad hoc and chaotic. It looks more akin to our original definition (the one that used `head` and `tail`) and I wouldn't be very surprised if I made an error here or there...

Papers:
- There are quite a few papers on mixing coinduction with induction, but most of them are written in the old deprecated Agda-style coinduction, so they aren't that much useful. We are going to list them, nevertheless (this time in chronological order (oldest first), not in order of relevance):
- [Continuous Functions on Final Coalgebras](https://core.ac.uk/download/pdf/82531251.pdf)
- [REPRESENTATIONS OF STREAM PROCESSORS USING NESTED FIXED POINTS](https://arxiv.org/pdf/0905.4813.pdf)
- [Mixing Induction and Coinduction](https://www.cse.chalmers.se/~nad/publications/danielsson-altenkirch-mixing.pdf)
- [Subtyping, Declaratively: An Exercise in Mixed Induction and Coinduction](https://www.cse.chalmers.se/~nad/publications/danielsson-altenkirch-subtyping.pdf)
- [Mixed Inductive-Coinductive Reasoning](https://liacs.leidenuniv.nl/~basoldh/thesis/Thesis.pdf) (PhD thesis from 2016, 340 pages, probably the best place to look for more papers on the topic, also probably contains a good introduction and overview)
- [The Size-Change Principle for Mixed Inductive and Coinductive types](https://arxiv.org/pdf/1901.07820.pdf)
- [Integrating Induction and Coinduction via Closure Operators and Proof Cycles](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC7324239/)

Other papers:
- [Mixed Inductive/Coinductive Types and Strong Normalization](http://www2.tcs.ifi.lmu.de/~abel/aplas07.pdf)
- [Type-Based Termination, Inflationary Fixed-Points, and Mixed Inductive-Coinductive Types](https://arxiv.org/pdf/1202.3496.pdf)
- [Termination Checking in the Presence of Nested Inductive and Coinductive Types](https://www.cse.chalmers.se/~nad/publications/altenkirch-danielsson-par2010.pdf)

**Status: mostly speculation, but based on the solid positive coinductive syntax sugar and solid principles. It looks mostly doable.**

TODO:
- Does `let` and copattern matching play out together as nicely as in the last example?
- Reconsider the `mutual` keyword for mutual coinductive-inductive definitions.
- Special syntax for (co)inductive types in which some recursive arguments are to be interpreted inductively and others coinductively.
- Untangleable coinduction-induction?
- Untangleable coinduction-coinduction?
- Make sure everything is syntactically up-to-date.

### Types with inductive and coinductive components <a id="inductive-coinductive-components"></a> [↩](#toc)

In the previous section we have seen two mutually defined types that looked exactly alike, `SP` and `GetSP`, the only difference being that `SP` was coinductive whereas `GetSP` was inductive. This is somewhat bad, because it leads to code duplication - for example, in our second implementation of `toStream` and `toStream'`, both these functions look identical.

This leads us to consider types in which self-referring occurrences can be either inductive or coinductive. Functions operating on these types must be recursive or corecursive, depending on the particular usage.

```
data Tree (A : Type) : Type
| E
| N of (v : A, l : Tree A, codata r : Tree A)
```

The above represents an inductive binary tree whose left subtree is also inductive, but whose right subtree is coinductive, i.e. potentially infinite.

```
map (f : A -> B) : Tree A -> Tree B
| E       => E
| N x l r => N (f x) (map l) (map r)
```

Papers:
- There are some papers with the old Agda coinduction which are somewhat akin to what is described here, but no papers exist specifically on this topic, I think. In case of doubt, look at the papers from previous section.

**Status: extremely speculative.**

TODO:
- Write something.

## Shared blocks, sections and automatic abstraction over parameters <a id="sections"></a> [↩](#toc)

We have already seen the usefulness of `mutual` blocks - they can greatly reduce the amount of code we need to type in case the mutually defined types or functions share many parameters.

We have two similar mechanisms that are useful for situations when there is no mutual induction/recursion. These are called "shared parameters" and "section".

```
shared ListFunctions
  (#A : Type)
  (p : A -> Bool)

  filter : List A -> List A
  | [] => []
  | h :: t with p h
    | tt => h :: filter t
    | ff => filter t

  all : List A -> Bool
  | [] => tt
  | h :: t => p h && all t

  any : List A -> Bool
  | [] => ff
  | h :: t => p h || any t
```

In the above snippet, we have used the `shared` keyword to define a few list functions which all work for a given type `A` and a `Bool`ean predicate `p : A -> Bool`. We list these parameters right after we open the `shared` block and then we define the functions like usual, just without mentioning the parameters.

```
> :t filter
filter : (#A : Type, p : A -> Bool) -> List A -> List A

> :t all
all : (#A : Type, p : A -> Bool) -> List A -> Bool

> :t any
any : (#A : Type, p : A -> Bool) -> List A -> Bool
```

After the `shared` block is closed, all of its parameters are abstracted in all definitions in the block (if a parameter is not used, it will be abstracted anyway) and these definitions are added to the global context.

```
> :def ListFunctions.filter
Listfunctions.filter
  : (#A : Type, p : A -> Bool) -> List A -> List A
  := filter

> :def ListFunctions.params
ListFunctions.params
  : Type
  := (#A : Type, p : A -> Bool)
```

The whole `shared` block is called `ListFunctions`. It is actually a namespace, in which we can find the functions we defined (well, in fact these are just aliases pointing to the functions we defined, which live in the global context) and a record type that collects all parameters that were abstracted over.

```
shared ListFunctions
  ...
end ListFunctions
```

Optionally, `shared` blocks can be ended with the `end` keyword. If we use it, we can also optionally include the name of the block the we want to `end`.

```
section OtherListFunctions
  #(A B : Type)
  (f : A -> B)

  len : List A -> Nat
  | [] => z
  | _ :: t => s (len t)

  app : (l1 l2 : List A) -> List A
  | []    , _ => l2
  | h :: t, _ => h :: (app t l2)

  map : List A -> List B
  | [] => []
  | h :: t => f h :: map t

end OtherListFunctions
```

The other kind of grouping mechanism is called a `section`. It works similarly to sections known from Coq and Lean - after the block is opened, we list the parameters and then we define the functions. At the end, we can optionally end the block with the `end` keyword and, also optionally, the block's name.

```
> :t len
len : (#A : Type) -> List A -> Nat

> :t app
app : (#A : Type) -> (l1 l2 : List A) -> List A

> :t map
map : #(A B : Type) (f : A -> B) -> List A -> List B
```

After the `section` is closed, all of its parameters are abstracted in all definitions in the section, but this time, in contrast to `shared` blocks, if a parameter is not used, it will NOT be abstracted. The definitions are then added to the global context.

```
> :def OtherListFunctions.len
OtherListfunctions.len
  : (#A : Type) -> List A -> Nat
  := len

> :def OtherListFunctions.params
OtherListFunctions.params
  : Type
  := #(A B : Type) (f : A -> B)

> :def OtherListFunctions.len.params
  : Type
  := (#A : Type)
```

A section must have a name - the above is called `OtherListFunctions`. Just as for `shared` blocks, the section is actually a namespace, in which we can find aliases for the functions we defined and a record type that collects all the parameters. This time, however, we can also find there record types corresponding to the parameters that were abstracted over in each particular definition, like `OtherListFunctions.len.params` above.

```
shared SharedIndicesAndSort
  parameters
  & A : Type

  indices
  & n : Nat

  sort Type

  data Vec
  | Nil  : Vec 0
  | Cons : (hd : A, #n : Nat, tl : Vec n) -> Vec (s n)

  data IBTree
  | E : IBTree 0
  | N : (root : A) #(hl hr : Nat) (l : IBTree h1, r : IBTree h2) -> IBTree (s (max hl hl))
```

We can use `shared` blocks not only to define functions, but also to define types. In these `shared` blocks we can share not only parameters, but also `indices` and the `sort` of the type being defined. Note: if we declare `indices` or `sort` in a `shared` block, we can't define functions in this block, since `shared` blocks must abstract over everything they contain.

```
section SectionWithIndicesAndSort
  parameters
  & A B : Type
  & f : A -> B

  indices
  & n : Nat

  sort Type

  data List
  | Nil
  | Cons of (hd : A, tl : List)

  data Vec
  | Nil  : Vec 0
  | Cons : (hd : A, #n : Nat, tl : Vec n) -> Vec (s n)

  data IBTree
  | E : IBTree 0
  | N : (root : A) #(hl hr : Nat) (l : IBTree h1, r : IBTree h2) -> IBTree (s (max hl hl))

  mapl : (l : List A) -> List B
  | Nil  => Nil
  | Cons => Cons (f l.hd) (mapl l.tl)

  mapv : (#n : Nat, v : Vec A n) -> Vec B n
  | Nil  => Nil
  | Cons => Cons (f v.hd) (mapv v.tl)

  mapibt : (#h : Nat, t : IBTree A h) -> IBTree B h
  | E => E
  | N => N (f t.root) (mapibt t.l) (mapibt t.r)
```

Last but not least, we can also use the `indices` and `sort` keyword in `section`s. This time, because `section`s abstract only over whatever is used by a particular definition, we can define functions inside a `section` which declares `indices` and/or a `sort`.

**Status: sections are implemented in Coq and Lean, and work more or less well there (I think from time to time there are some section-specific problems). The namespace-like character of `section`s is not present in these languages, but should be easy to implement, given that namespace work as intended. `shared` blocks are a novel idea of mine, but they are very analogous to `section`s, so if we can get `section`s to work, `shared` blocks will be easy too.**

Not papers:
- [Sections in Lean](https://leanprover.github.io/theorem_proving_in_lean/dependent_type_theory.html#variables-and-sections)
- [More about sections in Lean](https://leanprover.github.io/theorem_proving_in_lean/interacting_with_lean.html#more-on-sections)
- [Sections in Coq](https://coq.inria.fr/refman/language/core/sections.html)

TODO:
- Move the section on `section`s to the section on basic syntax (or to that on "advanced syntax").

## Refinement types <a id="refinements"></a> [↩](#toc)

The idea is to have, for every type `A`, the type `{x : A | P}` where `P` is some decidable strict proposition that the typechecker (or some external SMT solver, but that's meh...) can reason about. The pioneer in this space is [the F* language](https://www.fstar-lang.org/).

Some nice features related to refinement types that make life a lot easier are the already-described discriminators for inductive (and positive coinductive) types.

Another thing we can use refinement types for is to define _constructor projections_. These are like the usual projections for records, but they take fields out of inductive types' constructors, provided that an element was made with the appropriate constructor.

For `Nat`, there's a single projection

```
s?.pred : {n : Nat | s? n} -> Nat
```

which could be manually defined as

```
s?.pred {n : Nat | s? n} -> Nat
| s n' => n'
```

Note that the type `{n : Nat | s? n}` is treated just like `Nat`, so we can pattern match on terms of this type, but it also gives us (and the typechecker) some additional knowledge, so that we don't need to consider the case `z`, because the refinement guarantees that the argument can't be `z`.

For lists, the projections are

```
::?.hd : {l : List A | ::? l} -> A
::?.tl : {l : List A | ::? l} -> List A
```

which could manually be implemented as follows.

```
::?.hd {l : List A | ::? l} -> A
| h :: _ => h
```

As was the case for `s?.pred`, we don't need to consider the `[]` case, because the refinement `::? l` guarantees that it can't happen.

Additionally, we could also have another projection that projects out all arguments of `::` at once.

```
un-:: : {l : List A | ::? l} -> (hd : A, tl : List A)
```

This one could be manually implemented as

```
un-:: {l : List A | ::? l} -> (hd : A, tl : List A)
| h :: t => (hd => h, tl => t)
```

Tutorials and notes:
- [Programming with Refinement Types: An Introduction to LiquidHaskell](https://ucsd-progsys.github.io/liquidhaskell-tutorial/) - a nice introduction to the Liquid Haskell language, which is basically Haskell + refinement types
- [Proof-Oriented Programming in F*](https://www.fstar-lang.org/tutorial/) - the new F* tutorial. Looks bad now (in comparison with the old tutorial), but will probably get better in the future.
- [Principles of Type Refinement (OPLSS 2016)](http://noamz.org/oplss16/refinements-notes.pdf) - a theoretical tutorial on refinement types and their relationship with subtyping and intersection types
- [Refinement Types](https://arxiv.org/pdf/2010.07763.pdf) - a tutorial that shows how to implement a simple functional language with refinement types
- [INTEGRATING REFINEMENT AND DEPENDENT TYPES: A FELLOWSHIP REPORT](https://www.tweag.io/blog/2021-02-05-refinement-types/) - the only note I can find which discusses the fact that dependent types subsume refinement types

Papers:
- [Refinement Types for ML](https://www.cs.cmu.edu/~fp/papers/pldi91.pdf)
- [Liquid Types](http://goto.ucsd.edu/~rjhala/liquid/liquid_types.pdf)
- [Refinement Types For Haskell](https://goto.ucsd.edu/~nvazou/refinement_types_for_haskell.pdf)
- [Abstract Refinement Types](http://goto.ucsd.edu/~rjhala/liquid/abstract_refinement_types.pdf)
- [Functional Extensionality for Refinement Types](https://arxiv.org/pdf/2103.02177.pdf)
- [Refinements of Futures Past: Higher-Order Specification with Implicit Refinement Types](https://drops.dagstuhl.de/opus/volltexte/2021/14061/pdf/LIPIcs-ECOOP-2021-18.pdf)

Tangentially related blog posts:
- [Poltergeist Types](https://gallais.github.io/blog/poltergeist-types)

**Status: the only dependently-typed language with refinement types I know is F\*. The refinement types work pretty well there.**

TODO:
- Figure out the precise relationship between refinement types and dependent records with fields in `Prop`.
- Figure out relationship between refinement types and inductive/coinductive types. Hint: looks like there is no relationship for coinductives, but for inductives, the refinements should distribute over the constructors.
- Figure out the relationship between refinement types and ornaments.

## [Universes](Universes/Universes.md) <a id="universes"></a> [↩](#toc)

We want our universes to keep track of types' homotopy levels. This could:
- Give us more computational equalities by explicitly marking types as "strict propositions" (no computational content, i.e. all terms computationally equal), "strict sets" (paths are strict propositions) and so on. We call universes that are capable of this **strict universes**.
- Free us from boilerplate stemming from having to pass around proofs of being a proposition (`isProp`), a set (`isSet`) and so on and having to use them where appropriate. We call universes that are capable of this **non-strict universes**.

Of course, besides homotopy levels, we want to also keep track of the usual levels, which we will call _predicative levels_. This means that our universe hierarchy is going to be multidimensional, stratified both by homotopy levels and predicative levels, similar to the [Arend language](https://arend-lang.github.io/about/arend-features#universe-levels). In fact, there will be (at least) two type hierarchies: the strict one and the non-strict one.

### Syntax

We denote the strict universes by `Type h p`, where `h` is the homotopy level and `p` is the predicative level. We can be more explicit by writing `Type (h = h', p = p')`. We allow "typical ambiguity", i.e. when the level is not written, it will be inferred and solved by the universe checker. We can be more explicit and ambiguous at once, for example writing `Type (h = h')` - the homotopy level is explicit, but the predicative level will be inferred.

In the strict hierarchy, `Type (h = 0)` (abbreviated `Contr`) is the universe of (strict) contractible types (whose only member is itself), `Type (h = 1)` (abbreviated `Prop`) is the universe of strict (i.e. definitionally irrelevant) propositions (like Coq's [Prop](https://coq.inria.fr/refman/addendum/sprop.html) or Agda's [Prop](https://agda.readthedocs.io/en/v2.6.0/language/prop.html)), `Type (h = 2)` (abbreviated `Set`) is the universe of strict sets (types for which the type of paths is a strict proposition) and so on, up to `Type (h = oo)`, the universe of strict untruncated types.

The non-strict hierarchy (written `hType`) is similar. `hType (h = 0)` (abbreviated `hContr`) is the universe of homotopy contractible types (i.e. types which are contractible only up to a path), `hType (h = 1)` is the universe of (homotopy) propositions, `hType (h = 2)` is the universe of (homotopy) sets. The non-strict hierarchy is most similar to what we have in [Arend](https://arend-lang.github.io/about/arend-features#universe-levels) and also very similar to the hierarchy of `n`-Types from the HoTT Book.

We use Russell style universes because they are easier to read and write.

### Levels

The predicative levels are natural numbers and the homotopy levels are natural numbers extended with infinity (written `oo`). Whether levels stay at the metatheoretical level (nice pun, no?) or become first-class (by turning into the types `Nat` for p-levels and `hlvl` for h-levels) remains to be seen. In case we want it, we have `plvl : Set` (with `plvl` definitionally equal to `Nat`), `hlvl : Set` and we also need a universe `TYPE` which contains all universes `Type h p` and `hType h p` for all `h : hlvl` and all `p : plvl`.

Operations on levels include `pred` and `max`, which definitionally satisfy (or are defined as, in case levels are first-class) the following equations:

```
pred : hlvl -> hlvl
| 0     => 0
| l + 1 => l
| oo    => oo

max : (l1 l2 : hlvl) -> hlvl
| 0     , l2     => l2
| l1 + 1, l2     => max l1 l2 + 1
| oo    , l2     => oo
| l1    , 0      => l1
| l1    , l2 + 1 => max l1 l2 + 1
| l1    , oo     => oo
```

Some additional equations that should hold definitionally are `max l l = l` (idempotence) and `max l1 l2 = max l2 l1`.

The go-to paper for these considerations is [Generalized Universe Hierarchies and First-Class Universe Levels](https://arxiv.org/pdf/2103.00223.pdf).

### Basic mechanics of strict universes

The base case of our strict universe hierarchy is h-level 1, i.e. the universe of strict propositions. It's implementation is described in [Definitional Proof-Irrelevance without K](https://hal.inria.fr/hal-01859964v2/document).

```
// All proofs of a strict proposition are computationally equal.
isProp-from-Prop (#A : Prop) (x y : A) : x = y := refl
```

We then extend the hierarchy upwards. This is done with the formation rule for equality type/`Path` type, which says that if `A : Type h p` and `x y : A`, then `x = y : Type (pred h) p` (and similarly for `hType`; from now we will omit `hType` and concern ourselves only with `Type`). This crucially depends on the fact that `=` is a built-in path type and not an inductive family (if it were an inductive family, it would get placed in the wrong universe).

How this works in practice:

```
// `A : Set`, so `x = y : Prop` and so trivially `p = q`.
isSet-from-Set (#A : Set) #(x y : A) (p q : x = y) : p = q := refl

// Analogously for strict groupoids.
isGrpd-from-Grpd (#A : Grpd) #(x y : A) #(p q : x = y) (r s : p = q)
  : r = s := refl
```

At last, we need to return back to the zeroth level of the hierarchy and set up the universe `Contr`. The formation rule is `Contr : Contr` and it becomes fully functional when we allow cumulativity between `Contr` and `Prop`, i.e. `A : Contr` implies `A : Prop`. We might also consider dropping this unvierse completely, especially if we're worried by the `Contr : Contr` rule.

### Basic mechanics of non-strict universes

The typing rules for non-strict universes are analogous to those for strict universes, but the benefits are somewhat different - they amount to not needing to handle some cases when defining by pattern matching a function whose domain is known to be of some finite h-level.

This is because to define a function into an `n`-type, we only need to handle constructors of dimension less than or equal to `n - 1`. For example, when the codomain is a set, we only need to consider point constructors (obviously) and path constructors (so that we don't disconnect points which were connected), but not 2-dimensional path constructors (as all 2-paths in a set are equal).

These benefits multiply enormously when matching two or more values. For example, proving a property of two elements of a [free group defined like this](Induction/HIT/FG.ttw) requires only 9 cases instead of 49.

### Formation rules

| Name             | Rule             |
| ---------------- | ---------------- |
| Primitive types  | `i8, 16, i32, i64 : Type 2 0` <br> `u8, u16, u32, u64 : Type 2 0` <br> `f32, f64 : Type 2 0` <br> `Char : Type 2 0` <br> `Text : Type 2 0` |
| Arrays           | if `A : Type h p` <br> then `Array A n : Type h p` |
| Function type    | if `A : Type h1 p1` <br> and `B x : Type h2 p2` <br> then `(x : A) -> B x : Type h2 (max p1 p2)`  |
| Path type        | if `A : Type h p` <br> and `x y : A` <br> then `x = y : Type (pred h) p` |
| Name type        | if `A : Type h p` <br> then `Name A : Type 2 p` |
| Nominal function type | if `A : Type h1 p1` <br> and `B α : Type h2 p2` <br> then `∇ α : A. B α : Type h2 (max p1 p2)` |
| Empty type       | `Empty : Prop`  |
| Unit type        | `Unit : Contr`  |
| Record types     | if `A_i : Type h_i p_i` <br> then `(a_i : A_i) : Type (max h_i) (max p_i)` |
| Inductives       | see below           |
| Coinductives     | see below           |
| Refinements      | if `A : Type h p` <br> and `P : A -> Prop` <br> then `{x : A \| P x} : Type h p` |
| Singletons       | `Singleton A x : Contr` |
| Strict universes | `Type h p : Type (h + 1) (p + 1)` |
| Non-strict universes | `hType h p : hType (h + 1) (p + 1)` |
| Subtypes         | if `A : Type h p` <br> then `Sub A : Type (max 2 (h + 1)) p` |

Primitive types are strict sets at the `0`-th predicative level. Arrays inherit both the homotopy and the predicative level from the type of their elements.

Function types inherit their h-level from their codomain and their predicative level is the maximum of their domain's and codomain's levels. The same rule holds for nomnal function types. Names have decidable equality, so it only makes sense for `Name A` to be a strict set. Path types lower their h-level by one (unless it's already `0`, in which case it stays `0`) and preserve the predicative level of their codomain.

`Empty` is a strict proposition and `Unit` is contractible. Records are placed in the `max`imal universe of their (h and p)-levels.

Refinement types stay at the same levels as they carry just a proof of a strict proposition. Singleton types, understandably, live in the universe of strict contractible types.

For inductive types, tt is easy to determine the h-level of constructor arguments (since they are records; note that we need to ignore the inductive arguments), but for the whole type some heuristics are needed. If there are at least two constructors, the h-level is at least 2 (i.e. the type is a strict set), provided that there aren't any path constructors nor additional computation rules. It may well be that the constructor's arguments are disjoint (like `P` and `~ P`), but in general this is undecidable, so we don't care. If constructors are disjoint (i.e. we're not dealing with a higher inductive type) then the h-level will be maximum of 2 and the constructors' h-levels. If we're dealing with a HIT, things become infinitely more complicated and we may just as well say that the h-level of the whole type is `oo`.

Coinductive types can be handled similarly to records, but we need to ignore the h-level of coinductive fields when taking the `max`imum.

The universes themselves live in a universe whose levels are greater by one. The universe of strict contractible types `Contr` is a strict proposition, the universe of strict propositions `Prop` is a strict set, the universe of strict sets `Set` is a strict groupoid and so on.

A more interesting case is that of subuniverses. For `Empty` the type `Sub Empty` is contractible, but for non-empty types it always has at least two elements (`Empty` and the type itself), so it's always at least a set. This is why the first argument of `max` is `2` in the typing rule.

Moreover, `Sub Bool` has `Bool` as an element, and there are precisely two paths `Bool = Bool`, so `Sub Bool` is not a set, but a groupoid. This suggests that `Sub` behaves similarly to universes, i.e. raises the h-level by one. This is why the second argument of `max` in the typing rule is `h + 1`.

### Truncation

If the h-level of a type cannot be determined, we can **truncate** the type, i.e. force it into the desired level. We can also truncate the type when the h-level is inferred to be greater than what we want.

This feature allows us to define the operation known under many names: propositional truncation/propositional reflection/Squash type/etc. Importantly, we can do this even if we don't have [Higher Inductive Types](Induction/HIT). We do this with the `%Truncated` directive.

```
// Propositional truncation.
%Truncated
data Squash (A : Type) : hProp
| sq of A

// Strict truncation.
%Truncated
data ||_|| (A : Type) : Prop
| |_| of A

// Also pretty useful one: strict set truncation.
%Truncated
data SetSquash (A : Type) : Set
| in of A
```

The price we must pay for non-strict truncation is that we can eliminate truncated types `A : hType h p` only when constructing elements of types `B : hType h' p'` with `h' <= h`, i.e. of the same or lower h-level.

### Restrictions on elimination of strict propositions

In Coq and Agda there's a restriction on elimination of strict propositions so as to avoid "spilling" the strictness into the outside world, which could result in nontermination, undecidability of type checking and falling into extensional type theory.

This restrction says that inductive strict propositions can be eliminated into ordinary `Type`s if they satisfy some simple critera, which in practice amount to saying that all strict propositions which can be eliminated are built from `Empty`, `Unit` and recursive functions which return either `Empty` or `Unit`. For us, this means that `Empty` and `Unit` can be eliminated into anything at all and that other strict propositions can be eliminated only into other strict propositions.

### Restriction on elimination of other strict inductive types

What are the restrictions on elimination of strict inductive types at or above the strict set level?

At higher h-levels the criterion for strict propositions generalizes to the criterion that `Type h p` can be eliminated only into `Type h' p'` where `h' <= h`. For example, we can eliminate strict sets into strict sets and strict propositions (and also strict contractible types), but not into strict grupoids or non-strict types.

But is this really the case? This would mean that we can't define a family of strict sets whose domain are the strict natural numbers. Yuck!

```
data SNat : Set
| z
| s of (pred : SNat)

// This is certainly legal.
even : SNat -> Prop
| z       => Unit
| s z     => Empty
| s (s n) => even n

// Why would this be evil?
even : SNat -> Type
| z       => Unit
| s z     => Empty
| s (s n) => even n

// Legal.
data Even : SNat -> Prop
| Ez  : Even z
| Ess : (#n : SNat, e : Even n) -> Even (s (s n))

// Illegal?
data Even : SNat -> Type
| Ez  : Even z
| Ess : (#n : SNat, e : Even n) -> Even (s (s n))

// This definition looks quite illegal: `n = m : Prop` but `P m : Type`.
transport (#P : SNat -> Type) #(n m : SNat) (x : P n) : n = m -> P m
| refl => x

Zero-not-Succ (#n : SNat) (p : z = s n) : Empty :=
let
  P : SNat -> hType
  | z => Unit
  | _ => Empty

  x : P z := unit
in
  transport P x p
```

So maybe we are free to eliminate strict sets into any type whatsoever and the restrictions only apply to strict propositions? I have no idea.

### Summary

I have no idea what I'm doing. If something is not described here, it defaults to how it works in [Arend](https://arend-lang.github.io/about/arend-features#universe-levels).

Papers:
- [Definitional Proof-Irrelevance without K](https://hal.inria.fr/hal-01859964v2/document)
- [A type theory with definitional proof-irrelevance](https://www.theses.fr/2019IMTA0169.pdf) (for strict universes, see section 6.3)
- [Generalized Universe Hierarchies and First-Class Universe Levels](https://arxiv.org/pdf/2103.00223.pdf)
- [Notes on Universes in Type Theory](http://www.cs.rhul.ac.uk/home/zhaohui/universes.pdf)
- [Algebraic Type Theory and Universe Hierarchies](https://arxiv.org/pdf/1902.08848.pdf)

TODO:
- Write some code dealing with universes.
- Maybe merge strict and non-strict universes into one, i.e. `Type s h p`, with `s` being the strict (homotopy) level, `h` the (non-strict) homotopy level and `p` the predicative level? Of course we will then have `h <= s`.
- Rethink the formation rules for universes. I think the universe `Contr` shouldn't live in `Contr`, but rather in `hContr` - all singletons are equivalent, but we can't just computationally equate `Unit` with the type of sorting functions...
- Rethink when can strict inductive types be eliminated.

## Subtyping, coercions and subtype universes <a id="subtyping"></a> [↩](#toc)

We want to have subtyping in our type theory, but we want to avoid all the pitfalls associated with subtyping. For this reason, our subtyping judgement shall be proof-relevant, i.e. it should explicitly specify the coercion used to pass from the subtype to the supertype. The judgement is written `c : A <: B` and means that `c` is a coercion from `A` to `B`. These coercions should be unique, i.e. there can't be two coercions from `A` to `B`.

It should also be possible to declare custom coercions, as long as they don't break uniqueness. This, however, is a bit more problematic, because if we allow this then we need coercion management when importing modules etc.

Papers:
- [Luo's thesis](http://www.cs.rhul.ac.uk/home/zhaohui/ECS-LFCS-90-118.pdf) (see here for [a book version of the thesis](https://global.oup.com/academic/product/computation-and-reasoning-9780198538356?cc=gb&lang=en&)) describes ECC, a variant of the Calculus of Constructions which includes coercive subtyping.
- [Coercive subtyping: Theory and implementation](https://hal.archives-ouvertes.fr/hal-01130574/document)
- [Coherence and transitivity in coercive subtyping](https://core.ac.uk/download/pdf/6116522.pdf)

**Status: Coercions have been implemented in Coq for a long time. Implicit coercions between primitive types are standard in a lot of languages.**

### Subtype Universes

We shall reify the subtyping judgement into a type. The basic idea is that for every type `A` there is a type `Sub A` which represents the universe of subtypes of `A`. The only serious use for this feature presented in the relevant paper is simulating bounded polymorphism and extensible records.

```
translateX (n : Nat) (r : Sub (x : Nat)) : R :=
  (x $=> (+ n), _ => r)
```

Here we translate the `x`-coordinate by `n` in any record that has a field named `x`, while making sure to return a record of the same type without truncating it.

Subtyping for subtype universes is very simple - if `A` is a subtype of `B`, then the universe of subtypes of `A` is a subtype of the universe of subtypes of `B`.

Papers:
- [Subtype Universes](http://www.cs.rhul.ac.uk/home/zhaohui/Subtype%20Universes.pdf)

**Status: the paper is well-written and easy to understand, but there is no prototype, so it's mostly somewhat substantiated speculations.**

TODO:
- Find out how subtype universes interact with records.
- Find out how subtype universes work, at all.

### Subtyping rules

We summarize the rules that govern subtyping in the table below.

| Name              | Rule             | Coercion         |
| ----------------- | ---------------- | ---------------- |
| Primitive signed integers | `i8 <: i16 <: i32 <: i64` | built-in: copy the bits and pad the result with zeros |
| Primitive unsigned integers | `u8 <: u16 <: u32 <: u64` | built-in: copy the bits and pad the result with zeros |
| Primitive floats  | `f32 <: f64` | built-in |
| Coercions between signed and unsigned integers | `u8 <: i16` <br> `u16 <: i32` <br> `u32 <: i64` | built-in |
| Char and Text     | `Char <: Text` | make single character text |
| Arrays            | if `c : A <: A'` <br> and `n' <= n` <br> then `Array A n <: Array A' n'` | `map c` and clip the result to the correct length |
| Function type     | if `f : A <: A'` <br> and `g : B <: B'` <br> then `A' -> B <: A -> B'` | `fun h => f >> h >> g` |
| Paths             | if `c : A <: B` <br> then `x ={A} y <: c x ={B} c y` | `fun p => path i => c (p i)` |
| Name              | no subtyping | none |
| Nominal function type | if `c : A <: B` <br> then `∇ α : N. A <: ∇ α : N. B` | `fun x => ν α. c (x @ α)` |
| `Empty`           | `Empty <: A`     | `abort` |
| `Unit`            | `A <: Unit`      | `fun _ => unit` |
| `Bool`            | `Bool <: Prop`   | `fun b : Bool => if b then Unit else Empty` |
| Depth-subtyping for refinement types | if `P -> Q` <br> then `{x : A \| P} <: {x : A \| Q}` | change the refinement |
| Projection subtyping for refinement types | `{x : A \| P} <: A` | forget the refinement |
| Depth-subtyping for singleton types | if `c : A <: B` <br> then `Singleton A x <: Singleton B (c x)` | `c`, somehow <br> or `fun _ => c x` |
| Projection subtyping for singleton types | `Singleton A x <: A` | `fun _ => x` |
| Strict Universes  | if `h1 <= h2` <br> and `p1 <= p2` <br> then `Type h1 p1 <: Type h2 p2` | lift |
| Non-strict Universes | if `h1 <= h2` <br> and `p1 <= p2` <br> then `hType h1 p1 <: hType h2 p2` | lift |
| Subtype universes | if `c : A <: B` <br> then `Sub A <: Sub B` | built-in <br> `c` magically works on subtypes |

Primitive types have very predictable subtyping - we only allow coercions that don't lose informatiomn, i.e. that are injective.

We allow subtyping for arrays, both through the element type and through length, i.e. longer array types are subtypes of shorter array types.

Subtyping for functions is standard: contravariant in the domain and covariant in the codomain. This transfers to function-like types, i.e. path types and nominal function types, which are covariant in their codomains, but invariant in their domains (as the interval/`Name` types don't have subtypes).

It's not entirely clear, however, what the correct rules for `Name` and `∇` are. For now `Name` is invariant, but nothing prevents it from being covariant: if `c : A <: B` then `Name A <: Name B` with coercion `map c` for some `map : (A -> B) -> Name A -> Name B`. If `Name` was covariant, then I think (but I'm not sure) that `∇` could be contravariant in its domain, just like the function type.

We have some subtyping for `Empty`, `Unit` and `Bool`. First, `Empty` is a subtype of any type because given `e : Empty` we can just `abort` it. Second, any type is a subtype of `Unit`, because we can just erase the term and return `unit`. Third, `Bool` is a subtype of `Prop` so that we can easily go from the world of decidable propositions to the world of all propositions.

For refinement types, we allow making the refinement less precise (depth subtyping) or dropping it altogether (width subtyping). The rules for singleton types are similar. We can make a singleton type less precise by going to a singleton in the supertype (depth subtyping) or we can drop the singleton altogether and go to the surrounding type (width subtyping).

We cannot have cumulativity between strict propositions and larger universes in order to obey the restrictions on elimination. For now this means there's cumulativity between `Contr` and `Prop`, then a **GIANT WALL**, and then cumulativity starts again from strict sets upwards. So we have `Type 0 p <: Type h p'` for `h = 0` or `h = 1` and `p <= p'`, then a **GIANT WALL**, and then `Type (2 + h) p <: Type (2 + h') p'` for `h <= h'` and `p <= p'`.

For non-strict universes things are simpler, as we don't need a giant wall to avoid spilling strictness, so the rule is just `hType h p <: hType h' p'` provided that `h <= h'` and `p <= p'`.

Additionally we have `Type (2 + h) p <: hType (2 + h) p`, i.e. we may go from a strict universe to a non-strict one if we are at or above the set level, but not the other way around.

Not very relevant papers:
- [Subtyping dependent types](https://www.sciencedirect.com/science/article/pii/S0304397500001754)

**Status: Universe cumulativity is semi-standard, as some proof assistants don't have it. Subtyping for records is standard in languages that have "structural" record types. Subtyping of anything else in type theory is mostly wild speculations.**

### Subtyping for records and sums

| Name              | Rule             | Coercion         |
| ----------------- | ---------------- | ---------------- |
| Width-subtyping for record types | `r1 & r2 <: r1` <br> `r1 & r2 <: r2` (if `r2` does not depend on `r1`) | `fun x => (_ => x)` in prototyping syntax <br> spelled out: just copy the relevant fields |
| Depth-subtyping for record types | if `c : A <: A'` <br> then `(a : A) <: (a : A')` | `fun x => (a => c x.a)` |
| Projection subtyping for records | `a : (a :> A) <: A` | Note: this only works if the field is declared as a coercion field |
| Manifest field subtyping | `(a : A := a') & r <: (a : A) & r` | `fun x => (a => x.a, _ => r)` <br> Only ok if nothing in `r` depends on the value of `a` |
| Compatility of subtyping with `&` | if `c1 : r1 <: r1'` <br> and `c2 : r2 <: r2'` <br> then `r1 & r2 <: r1' & r2'` | `fun x => (_ => c r1, _ => c r2)` |
| Another kind of compatibility | if `r1 <: r` <br> and `r2 <: r` <br> then `r1 & r2 <: r` | TODO |
| Advanced subtyping for records | [complicated](Records/TurboRecords.ttw) | |
| Width-subtyping for sums | `s1 <: s1 \| s2` <br> `s2 <: s1 \| s2` | TODO |
| Depth-subtyping for sums | if `c : A <: A'` <br> then `[a : A] <: [a : A']` | `fun x => a (case x of \| a v => c v)` |
| Injection subtyping for sums | `a : A <: [a :> A]` | Note: this only works if the constructor is declared as a coercion constructor |
| Compatibility of subtyping with `\|` | if `c1 : s1 <: s1'` <br> and `c2 : s2 <: s2'` <br> then `s1 \| s2 <: s1' \| s2'` | TODO |
| Another kind of compatibility | if `s <: s1` <br> and `s <: s2` <br> then `s <: s1 \| s2` | TODO |

The basic subtyping rules for records are the same as in other languages, i.e. we have width subtyping (bigger record types are subtypes of smaller record types) and depth-subtyping (record types with subtype fields are subtypes of record types with supertype fields). Records types with manifest fields are subtypes of records types in which these fields are not manifest.

As far as projections are concerned, we can't make all of them into coercions, because it would break uniqueness. For example, consider the product `A * B` (which is defined as the record `(outl : A, outr : B)`). If we made both `outl` and `outr` into coercions, then for `A * A` we have `outl : A * A <: A` and also `outr : A * A <: A`, which means uniqueness doesn't hold.

Moreover, we can't automatically make any projection into a coercion, even if the record has only a single field, because the above problem would reappear. In such a scenario for `A * A` we would have `(outl : A, outr : A) <: (outl : A) <: A` and also `(outl : A, outr : A) <: (outr : A) <: A`, so uniqueness wouldn't hold.

The solution to this problem is surprisingly simple. We introduce a distinction between a non-coercion field, written `a : A` as usual, and a coercion field, written `a :> A`. The difference is that the latter field declares the field `a` a coercion from the whole record to the type `A`, whereas the former does not. So we have `a : (a :> A) <: A`, but not `(a : A) <: A`. The types `(a : A)` and `(a :> A)` are isomorphic (and thus equal, by univalence), but not computationally equal.

Equipped with new syntax for coercion fields, all it takes to solve the previous problem is to decide which fields we want to designate as coercions and which ones we don't. The only criterion for whether our choice is valid is that uniqueness must hold.

As an example, consider (a part of) the type of vector spaces `VectorSpace := (V : Type, S : Type, ...)`. `V` (the type of vectors) and `S` (the type of scalars) can't be both coercions, because then we have `VectorSpace <: Type` into two different ways. But since when writing `v : A` for `A : VectorSpace` we usually mean `v : A.V`, it makes sense to turn `V` into a coercion. So we instead define `VectorSpace := (V :> Type, S : Type, ...)`, which means that the only way to interpret a vector space as a type is to interpret it as its type of vectors.

Subtyping rules for sums are dual to those for records. There's width subtyping (smaller sums are subtypes of bigger sums) and depth-subtyping (sums whose constructors take subtypes are subtypes of sums whose constructors take supertypes).

As with record, constructors can't be coercions by default, because it would break uniqueness. Consider, for example, the sum type `A + B`, defined as `A + B := [inl : A, inr : B]`. If both `inl` and `inr` were coercions, then for `A + A` we have `inl : A <: A + A` and also `inr : A <: A + A`, so uniqueness doesn't hold.

In the other direction and analogously to what was the case for records, we can't automatically make constructors into coercions even for sums with only one constructor. If we did, then `A <: [inl : A]`, but also `A <: [inr : A]`, so that `A <: [inl : A, inr : A]` into two different ways.

The solution is the same as for records: we have ordinary constructors, written `[a : A]`, and coercion constructors, written `[a :> A]`, which make `a` into a coercion from `A` to `[a :> A]`. We can then manually decide which constructors are coercions and which are not, the only criterion to be satisfied being uniqueness.

As an example, consider the syntax of a language that has natural constants and variables represented as naturals, `L := [Var : Nat, Const : Nat]`. Since it makes more sense to consider `42` to be just a number (i.e. `Const 42`) than a variable (i.e. `Var 42`), we can mark `Const` as a coercion by writing `[Var : Nat, Const :> Nat]`.

TODO:
- Subtyping rules for advanced records that behave like functions (i.e. have manifest fields whose value depends on another field).

### Subtyping for inductive and coinductive types

| Name              | Rule             | Coercion         |
| ----------------- | ---------------- | ---------------- |
| Inductives        | The rules for sums and then some more |
| Unfolding-subtyping for inductives | `μ X. F X <: F (μ X. F X)` | Autogenerated case analysis principle |
| Base functor subtyping for inductives | if `c : F X <: G X` for all `X` <br> then `μ X. F X <: μ X. G X` | TODO: recursively extend `c` |
| Coinductives      | The rules for records and then some more |
| Unfolding-subtyping for coinductives | `ν X. F X <: F (ν X. F X)` | TODO |
| Base functor subtyping for coinductives | if `F X <: G X` for all `X` <br> then `ν X. F X <: ν X. G X` | TODO: corecursively extend `c`  |
| Inductive-coinductive subtyping | `μ X. F X <: ν X. F X` | TODO |

Subtyping for inductive and coinductive types works similarly to that for sums and records. The details are not entirely clear to me yet, but I have a few ideas.

Subtyping for coinductives needs to be more restrictive than that for records in order to guarantee that uniqueness holds in all cases. Consider the type of streams (with some coercions added), `CStream A := (hd :> A, tl :> CStream A)`. We have `CStream A <: A` through `hd`, but also `CStream A <: CStream A <: A` through `tl >> hd` and these two coercions are not (definitionally) equal.

We can probably rescue this situation if we disallow coercion fields from a coinductive type `C` to itself. For example, if `tl` is not allowed to be a coercion, then `hd` can safely be one.

But this rule is not general enough. Consider a coinductive type `C`. If `C` has a field `cs : (outl :> C, outr : Bool)`, then `cs` can't be a coercion, because if it were, then we would have `C <: (outl :> C, outr : Bool) <: (outl :> C) <: C`, which is bad.

In general, a field whose type is a subtype of `C` can't be a coercion. Dually, a constructor whose argument is a supertype of `I` can't be a coercion from that type into `I`. As long as these conditions hold, subtyping for inductive and coinductive types coincides with subtyping for sums and records.

Papers:
- [Subtyping and Inheritance for Inductive Types](https://www.cs.ru.nl/E.Poll/papers/durham97.pdf)
- [Subtyping and Inheritance for Categorical Datatypes](https://www.cs.ru.nl/E.Poll/papers/kyoto97.pdf)
- [Constructor Subtyping in the Calculus of Inductive Constructions](https://www.researchgate.net/publication/221570140_Constructor_Subtyping_in_the_Calculus_of_Inductive_Constructions)
- Proof Reuse with Extended Inductive Types (no link)

Less relevant papers:
- [Structural subtyping for inductive types with functorial equality rules](https://www.cs.rhul.ac.uk/home/zhaohui/Trans2.pdf)
- [Induction, Coinduction, and Fixed Points in Programming Languages (PL) Type Theory](https://arxiv.org/pdf/1903.05126.pdf)
- [Revisiting Iso-Recursive Subtyping](https://dl.acm.org/doi/pdf/10.1145/3428291)

**Status: very speculative.**

TODO:
- If `c : A <: B` then we have `List A <: List B`, but to state the coercion here we first need to have defined `map : (A -> B) -> List A -> List B`, which is baaaad.

### Strong vs weak specifications

One nice consequence of our subtyping rules for inductive types is that types of strongly-specified programs are (or can be made into, depending on constructor's chosen names) subtypes of types of weakly-specified programs. This solves (or at least diminishes) a long-lasting clash between strong and weak specifications.

```
data Answer : Type
| Yes
| No

data Option (A : Type) : Type
| Yes of A
| No

data Decision (P : Type) : Type
| Yes of P
| No  of ~ P
```

Consider the above definitions of `Answer`, `Option` and `Decision`. `Answer` is a renamed version of `Bool`, with `Yes` instead of `tt` and `No` instead of `ff`. `Option` is defined as usual in ML languages and represents the presence of a value (`Yes v`) or lack of a value (`No`). `Decision P` is an analogue of Coq's `sumbool` and represents a decision procedure for the proposition `P`, where the `Yes` constructor carries a proof of `P` and the `No` constructor carries a proof of `~ P`.

We have `Decision P <: Option P <: Answer` thanks to the autogenerated coercions, which could be manually implemented as

```
%Coercion
Dec2Opt : Decision P -> Option P
| Yes y => Yes y
| No  _ => No

%Coercion
Opt2Ans : Option A -> Answer
| Yes _ => Yes
| No    => No
```

Let's see how this can be used in practice. Let's say we implement a function to remove consecutive duplicated elements from a list, similar to `dedupConsecutive` from before.

```
dedupConsecutive (#A : Type, eq : A -> A -> Bool) : List A -> List A
| []          => []
| [x]         => [x]
| x :: y :: t => if eq x y then dedupConsecutive (y :: t) else x :: dedupConsecutive (y :: t)
```

Now let's say we have proved that some type `A` has decidable equality, i.e. we have `dec : (x y : A) -> Decision (x = y)`. Thanks to subtyping for inducive types, we can use `dec` in every place where a function `A -> A -> Bool` is expected.

```
// Assuming we have some x y z : A in the context.
dedupConsecutive dec [x, x, y, x, y, y, z, x, z, z]
```

**Status: this follows directly from the rules in the previous section.**

### Subtyping between inductive and coinductive types

We should have subtyping between an inductive type and a positive coinductive type with the same base functor. For example, `List A` should be a subtype of `CoList A`, where

```
data List (A : Type) : Type
| Nil
| Cons of (hd : A, tl : List)

codata CoList (A : Type) : Type
| Nil
| Cons of (hd : A, tl : CoList)
```

The coercion is of course

```
%Coercion
c : List A -> CoList A
| Nil      => Nil
| Cons h t => Cons h (c t)
```

Another example: natural numbers should be a subtype of the conatural numbers, where

```
data Nat : Type
| Z
| S of (pred : Nat)

codata CoNat : Type
| Z
| S of (pred : CoNat)
```

with the coercion being

```
%Coercion
c : Nat -> CoNat
| Z   => Z
| S n => S (c n)
```

**Status: very speculative, but looks easy to implement provided that basic subtyping already works.**

### Subtyping between negative and positive coinductive types

Positive coinductive types often represent data structures that are potentially infinite, whereas negative coinductive types often represent versions of these data structures that are necessarily infinite (for completeness, inductives represent versions of these data structures that are necessarily finite).

For example, `Stream`s are necessarily infinite, whereas `CoList`s are only potentially infinite (and `List`s are necessarily finite). Therefore it makes sense to ask whether there can be some subtyping between `Stream A` and `CoList A`. Certainly we can define a function `c : Stream A -> CoList A` and declare it a coercion, but having to do this every single time and for every pair of types would force us to write a lot of boilerplate.

We propose a different solution of this problem: we can declare a constructor name for negative coinductive types. This name is then used to determine subtyping relations for the type.

```
codata Stream (A : Type) : Type
constructor Cons
& hd of A
& tl of Stream

codata CoList (A : Type) : Type
| Nil
| Cons of (hd : A, tl : CoList)
```

The type family `Stream` defined as above is equivalent to our previous definition, but additionally we get an autogenerated function `Cons : (hd : A, tl : Stream A) -> Stream A`, so that we can write `Cons h t` and we need to use neither tuple syntax, nor copattern syntax, nor module syntax.

This `Cons` constructor, thanks to its name, induces an autogenerated coercion from `Stream`s to `CoList`s, which could be manually defined as follows.

```
%Coercion
c : (s : Stream A) -> CoList A :=
  Cons s.hd (c s.tl)
```

**Status: Agda (and Coq too, I think) provide the ability to choose the constructor's name when defining records and coinductive types. If the basic subtyping rules work as expected, it should be an easy walk from there.**

### Subtyping for (co)inductive families

We should also take care of subtyping rules for (co)inductive families. There are two main kinds of subtyping here:
- indexed families are subtypes of non-indexed types
- families indexed by subtypes are subtypes (or rather, subfamilies) of families indexed by supertypes

As an example of the first kind of subtyping, consider the types of vectors and lists.

```
data List (A : Type) : Type
| Nil
| Cons of (hd : A, tl : List)

data Vec (A : Type) : Nat -> Type
| Nil  : Vec z
| Cons : (hd : A, #n : Nat, tl : Vec n) -> Vec (s n)
```

We have `Vec A n <: List A` for all `n : Nat` due to an autogenerated coercion which could be manually implemented as

```
%Coercion
c : (v : Vec A n) -> List A
| Nil  => Nil
| Cons => Cons v.hd (c v.tl)
```

As an example of the second kind of subtyping, consider additionally the type of covectors, i.e. coinductive vectors indexed by conatural numbers.

```
codata Covec (A : Type) : CoNat -> Type
| Nil  : Vec z
| Cons : (hd : A, #n : CoNat, tl : Covec n) -> Covec (s n)
```

Because `Nat <: CoNat` and the constructor names (and constructors' fields' names) match, we have an autogenerated coercion `c : Vec A n <: Covec A n` (or more precisely `c : Vec A n <: Covec A (c' n)`, where `c' : Nat <: CoNat`). This coercion could be manually implemented as

```
%Coercion
c : (v : Vec A n) -> Covec A n
| Nil  => Nil
| Cons => Cons (hd => v.hd, n => v.n, tl => c v.tl)
```

### Subtyping for [Advanced Inductive Types](#advanced-inductive-types)

The more advanced genres of inductive types also enjoy some subtyping.

For every CIT (Computational Inductive Type) we can define its Associated Computation-Free Type (ACFT), which is an inductive types with the same constructors, but without the additional computation rules. The subtyping rule for CITs says that every CIT is a subtype of its ACFT.

For example, we have `Z <: Z'`, where `Z` is the type of integers we have seen before, defined as a computational inductive type, and `Z'` is its ACFT defined as follows.

```
data Z' : Type
| z
| s of (pred : Z)
| p of (succ : Z)
```

Of course, we want the other subtyping rules for inductive types to also apply to Computational Inductive Types. For example, we want to have `Nat <: Z`. To derive this subtyping judgement, we need to think about subtyping of sums and inductives in reverse direction.

To derive `Nat <: Z'` we can use the rule for base functor subtyping and we think of using it as "forward", i.e. `Nat` is a subtype of `Z'` because we can add the constructor `p` to `Nat` and to get `Z'`.

A similar way of thinking doesn't make much sense for Computational Inductive Types, because we would also need to think about adding computation rules, but then not all computation rules added to `Z'` will result in a supertype of `Nat` (one example is the rule `s z => z`). Instead, we need to think "backwards", i.e. we need to think that `Z'` is the supertype of `Nat` because we can remove the constructor `p` from it to get `Nat`. In a similar fashion, `Z` is a supertype of `Nat` because if we remove from `Z` the constructor `p` and all the computation rules it is mentioned in, we will get `Nat`.

The above examples of CIT subtyping are illustrative, but not illuminating. For the latter, we need to state the appropriate rules precisely. So far, the most basic rule for subtyping of sums was that adding constructors produces a supertype. Starting from there, the rules for CITs are:
- If we add a new computation rule to a (computational) inductive type, we get a subtype. In the other words, if we remove a computation rule, we get a supertype.
- If we add a new constructor (possibly with some computation rules) to an inductive type, we get a supertype.
- A slightly more powerful backwards version of the above rule is that if we remove a constructor and all computation rules that mention it from an inductive type, we get a subtype.

Subtyping for Higher Inductive Types works basically the same as for ordinary inductives, i.e. adding a path constructor produces a supertype. Note, however, that coercions into HITs no longer need to be injective. For example, the sum `A + B` is a subtype of the pushout of `f : C -> A` and `g : C -> B`, but the coercion is surjective.

There is nothing special going on with subtyping for Nominal Inductive Types, Inductive-Inductive Types and Inductive-Recursive Types.

**Status: very speculative.**

TODO:
- What is the relationship between computational inductive types and record types with manifest fields. Are these two dual to each other?
- Make sure there's really nothing special with NITs, IIT and IRT.

### Co-inheritance for inductive types

Co-inheritance is a mechanism for code reuse dual to OOP's inheritance (and also probably dual to our record prototyping). If we have `A <: A'`, then co-inheritance allows us to reuse the definition of a recursive function of type `A -> B` to define a recursive function of type `A' -> B`.

For example, consider the usual type of lists (renamed `ConsList`) and its supertype, the type `BiList` of lists which have an additional constructor for adding elements at the end.

```
data ConsList (A : Type) : Type
| Nil
| Cons of (hd : A, tl : ConsList)

data BiList (A : Type) : Type
| Nil
| Cons of (hd : A, tl : BiList)
| Snoc of (init : BiList, last : A)
```

We can define some useful functions for `ConsList`, like the function `len` which computes the length of a list.

```
len : ConsList A -> Nat
| Nil      => z
| Cons _ t => s (len t)
```

We can define a similar function for `BiList`. Note that there is some repetition - the cases for `Nil` and `Cons` are identical in both functions. Moreover, there is potentially a need to choose a unique name for the function, which would distinguish it from the previous `len`. This adds some thinking overhead (as every programmer knows, coming up with names is the hardest part of programming).

```
len' : BiList A -> Nat
| Nil      => z
| Cons _ t => s (len' t)
| Snoc i _ => s (len' i)
```

To avoid this repetition, we can `co-inherit` the definition of `len` when defining `len'` so that we only need to specify the missing `Snoc` case. Because `len` and `len'` give equal results for all `ConsList`s, there is no confusion between the two functions, so that we may just as well rename `len'` to `len` (this kind of ambiguity/ad-hoc overloading being, as you may recall, perfectly legal in our language).

```
len : BiList A -> Nat
| co-inherit len
| Snoc i _ => s (len i)
```

Besides just co-inheriting a definition at the face value, we can also overwrite some of its cases. In the function `len_plus_5` below, we overwrite the `Nil` case.

```
len_plus_5 : BiList A -> Nat
| co-inherit len
| Nil => 5
| Snoc i _ => s (len_plus_5 i)
```

The above function is equivalent to the below one, implemented manually.

```
len_plus_5 : BiList A -> Nat
| Nil => 5
| Cons _ t => s (len_plus_5 t)
| Snoc i _ => s (len_plus_5 i)
```

We haven't shown the full power of co-inheritance so far, because we only used it to co-inherit functions with domain `ConsList`. However, we can also use co-inheritance when the subtype occurs in the codomain. This is useful, for example, to implement the function `map` for `ConsList` (called `mapc`) and `BiList` (called `mapb`).

```
mapc (f : A -> B) : ConsList A -> ConsList B
| Nil => Nil
| Cons h t => Cons (f h) (mapc t)

mapb (f : A -> B) : BiList A -> BiList B
| co-inherit (mapc f)
| Snoc init last => Snoc (mapb init) (f last)
```

Even though `mapc` above has codomain `ConsList B`, this is fine because `ConsList B <: BiList B`, so we may freely co-inherit it when defining `mapb`.

Now, this is still not the full power of co-inheritance, because so far we have only used single co-inheritance. But multiple co-inheritance is possible too. Consider the type `SnocList` of lists which have no `Cons`, but only a `Snoc`.

```
data SnocList (A : Type) : Type
| Nil
| Snoc of (init : SnocList, last : A)
```

We can implement `map` for `SnocList`s.

```
maps (f : A -> B) : SnocList A -> SnocList B
| Nil => Nil
| Snoc i l => Snoc (maps i) (f l)
```

Using multiple co-inheritance, we can reuse both `mapc` and `maps` to define `mapb`. The definition of `mapb` below is equivalent to the previous one.

```
mapb (f : A -> B) : BiList A -> BiList B
| co-inherit (mapc f), (maps f)
```

The only condition that needs to be satisfied for multiple co-inheritance to be legal is that overlapping cases need to have the same result. For the above definition the only overlapping case is `Nil`. For both `mapc` and `maps` the result for the `Nil` case is `Nil`, although for `mapc` the `Nil` is of type `ConsList B`, whereas for `maps` the `Nil` is of type `SnocList B`. This is not a problem, however, because both `Nil`s are coerced to `Nil` of type `BiList B`, and so the results of `mapc` and `maps` for the `Nil` case are considered equal. Therefore our use of multiple co-inheritance is legal. However, if the condition of computationally equal results in overlapping cases is not met, we can easily dodge it by overwriting the conflicting cases.

The only other condition on co-inheritance is that we cannot use it to extend a function `f : A -> B` to a function `g : A' -> B` (where `c : A <: A'`) if the definition of `f` uses a helper function `h : A -> R`. However, we might dodge the above condition by first co-inheriting `h : A -> R` to define `h' : A' -> R` and then co-inheriting `f : A -> B` to define `g : A' -> B`.

**Status: very speculative, even relative to the very speculative nature of subtyping for inductive and coinductive types.**

## [Type-level rewriting](Rewriting) <a id="type-level-rewriting"></a> [↩](#toc)

Computational equality is good, so we would like to have more of it. We have already made `Empty` and `Unit` into strict propositions to make our lives easier - nobody likes having to pattern match on `u : Unit` just to learn that it's equal to `unit` (what a surprise!), just as nobody likes having to infer that two proofs of `Empty` are equal from contradiction.

But since computational equality is so good, we would like to have more of it also at the type level. In this section we list some additional computational equalities that we would like `Empty`, `Unit` and `=` to satisfy.

### Computational properties of the `Empty` type

Let's start with some computational properties of `Empty` and `+` (i.e. the usual inductive sum with `inl` and `inr` as constructors).

`Empty` is the left identity of `+`, i.e. `Empty + A = A`. In ordinary type theory this is easy to prove (as an equivalence) and with univalence also as an actual equality, but it's also a little bothersome, so we make it hold by computation.

```
Sum-Empty-l : Empty + A = A := refl
```

But this additional computational equality, if left alone, would break important properties of our type theory, like preservation of types by computation, so we also need to add some more computation at the term level to avoid it. Namely, since `Empty + A` computes to `A`, we need to know, for terms of type `Empty + A`, what terms of type `A` they compute to.

```
Sum-Empty-l-inl (e : Empty) : (inl e : Empty + A) = (abort e : A) := refl
Sum-Empty-l-inr (a : A) : (inr a : Empty + A) = a := refl
```

Of course `Empty` is also the right identity of `+`, so we have analogous computational equalities for that case too.

```
Sum-Empty-r : A + Empty = A := refl
Sum-Empty-r-inl (a : A) : (inl a : A + Empty) = a := refl
Sum-Empty-r-inr (e : Empty) : (inr e : A + Empty) = (abort e : A) := refl
```

For `*` (i.e. the binary product type), `Empty` is a left annihilator.

```
Prod-Empty-l : Empty * A = Empty := refl
```

But again, this equation alone breaks type preservation, so we need to add some more to restore this property.

```
Prod-Empty-l-outl (x : Empty * A) : x = x.outl := refl
```

We have analogous computational equalities for `*` and `Empty` on the right too.

```
Prod-Empty-r : A * Empty = Empty := refl
Prod-Empty-r-outr (x : A * Empty) : x = x.outr := refl
```

The above annihilation properties generalize to records.

```
Record-Empty (R : RType) : (e : Empty) & R = Empty := refl
Record-Empty-proj (R : RType) (x : (e : Empty) & R) : x = x.e := refl
```

These are not the only special computational properties of `Empty` - there are more.

Function types with `Empty` domain are the same as `Unit`.

```
Fun-Empty : Empty -> A = Unit := refl
Fun-Empty' (f : Empty -> A) : f = unit := refl
```

`Empty` is equal to `Empty` in a single canonical way.

```
Path-Empty : (Empty = Empty) = Unit := refl
Path-Empty' (p : Empty = Empty) : p = unit := refl
```

The nominal function with `Empty` codomain is `Empty`.

```
Nabla-Empty : (∇ α : A. Empty) = Empty := refl
```

But stating the appropriate term-level computation rule is a little difficult. First we need to define by pattern matching a function which pulls `Empty` from under the nabla.

```
anonymize-Empty (x : ∇ α : A. Empty) : Empty
| ν α. e => e
```

And only then we can state that every nominal function with `Empty` codomain is equal to its anonymization.

```
Nabla-Empty' (x : ∇ α : A. Empty) : x = anonymize-Empty x := refl
```

There's not much sense in putting refinements on `Empty`.

```
Ref-Empty (P : Empty -> Prop) : {e : Empty | P e} = Empty := refl
```

For the term-level computational equality, similarly to what was the case for nominal function type, we first need to have a function which gets rid of the refinement, and then state that every term of the refined `Empty` type is equal to an unrefined one.

```
// No definition.
unrefine #(A : Type, P : A -> Prop) : {a : A | P a} -> A

Ref-Empty' (P : Empty -> Prop) (x : {e : Empty | P e}) : x = unrefine x := refl
```

Singletons made from a term of type `Empty` are equal to `Empty` and their values are equal to the term they were made from.

```
Singleton-Empty (e : Empty) : Singleton Empty e = Empty := refl
Singleton-Empty' #(e : Empty) (x : Singleton Empty e) : x = e := refl
```

Finally, `Empty` has only one subtype (namely itself), so its universe of subtype is equal to `Unit`, and its only inhabitant is equal to `unit`.

```
Sub-Empty : Sub Empty = Unit := refl
Sub-Empty' (X : Sub Empty) (x : X) : x = unit := refl
```

### Computational properties of the `Unit` type

Another type that enjoys special computational properties is `Unit`.

First and foremost, `Unit` is the (left and right) identity of `*`.

```
Prod-Unit-l : Unit * A = A := refl
Prod-Unit-l-outr (x : Unit * A) : x = x.outr := refl

Prod-Unit-r : A * Unit = A := refl
Prod-Unit-r-outl (x : A * Unit) : x = x.outl := refl
```

These properties generalize to records.

```
Record-Unit (R : RType) : (u : Unit) & R = R := refl
Record-Unit' (R : RType) (x : (u : Unit) & R) : x ={R} (_ => x) := refl
```

Function types with `Unit` domain are equal to just their codomain.

```
Fun-Unit-Dom : Unit -> A = A := refl
Fun-Unit-Dom' (f : Unit -> A) : f = f unit := refl
```

Function types with `Unit` codomain are equal to `Unit`.

```
Fun-Unit-Cod : A -> Unit = Unit := refl
Fun-Unit-Cod' (f : A -> Unit) : f = unit := refl
```

`Unit` is equal to `Unit` is a single canonical way.

```
Path-Unit : (Unit = Unit) = Unit := refl
Path-Unit' (p : Unit = Unit) : p = unit := refl
```

Nominal function types with `Unit` codomain are equal to `Unit`. This time, contrary to what was the case for `Empty`, we don't need any kind of anonymization function.

```
Nabla-Unit : (∇ α : A. Unit) = Unit := refl
Nabla-Unit' (x : ∇ α : A. Unit) : x = unit := refl
```

`Unit` with refinements put on it is computationally equal to `Unit`.

```
Ref-Unit (P : Unit -> Prop) : {u : Unit | P u} = Unit := refl
Ref-Unit' (P : Unit -> Prop) (x : {u : Unit | P u}) : x = unrefine x := refl
```

### Computational properties of the Path type

Paths between pairs are pairs of paths.

```
Path-Prod (x y : A * B) : (x = y) = (outl x = outl y * outr x = outr y) := refl
Path-Prod' #(x y : A * B) (p : x = y)
  : p = (path i => outl (p i), path i => outr (p i)) := refl
```

Paths between records are records of paths.

```
Path-Rec #(A : Type, R : RType) (x y : (a : A) & R)
  : (x = y) = (a : x.a = y.a) & (r : x removing a = y removing a) := refl
Path-Rec' #(A : Type, R : RType) (x y : (a : A) & R) (p : x = y)
  : p = (a => path i => a (p i), r => path i => p i removing a) := refl
```

Paths between functions are homotopies (i.e. functions that return paths in the codomain).

```
Path-Fun (f g : (x : A) -> B x) : (f = g) = ((x : A) -> f x = g x) := refl
Path-Fun' #(f g : (x : A) -> B x) (p : f = g) : p = fun x : A => path i => p i x := refl
```

`Empty` is a strict proposition, so all paths between its terms are equal.

```
Path-Empty (e1 e2 : Empty) : (e1 = e2) = Unit := refl
Path-Empty' #(e1 e2 : Empty) (p : e1 = e2) : p = unit := refl
```

The same is true for `Unit`.

```
Path-Unit (u1 u2 : Unit) : (u1 = u2) = Unit := refl
Path-Unit' #(u1 u2 : Unit) (p : u1 = u2) : p = unit := refl
```

Paths between paths are squares.

```
Path-Path #(x y : A) (p q : x = y) : (p = q) = (path i j => p i = q j)
```

Paths between nominal functions are nominal functions that return paths.

```
Path-Nabla (x y : ∇ α : A. B α) : (x = y) = ∇ α. x @ α = y @ α := refl
Path-Nabla' #(x y : ∇ α : A. B α) (p : x = y) : p = ν α. path i => p i @ α
```

Paths between terms of a refinement type are the same as paths in its base type, after dropping the refinement.

```
Path-Ref (x y : {a : A | P a}) : (x = y) = (unrefine x ={A} unrefine y) := refl
Path-Ref #(x y : {a : A | P a}) (p : x = y) : p = path i => unrefine (p i)
```

Paths in singleton types are unique.

```
Path-Singleton #(A : Type, a : A) (x y : Singleton A a) : (x = y) = Unit := refl
Path-Singleton' #(A : Type, a : A, x y : Singleton A a) (p : x = y) : p = unit := refl
```

Because all singletons are, well, singletons, paths between singleton types are equal to `Unit`.

```
Path-Singleton #(A : Type, x y : A) : (Singleton A x = Singleton A y) = Unit := refl
Path-Singleton #(A : Type, x y : A) (p : Singleton A x = Singleton A y) : p = unit := refl
```

Ladies and gentlemen, the venerable champion, Univalence Principle!

```
Path-Type (A B : Type) : (A = B) = Equiv A B := refl
```

Paths between subtypes of some type are the same as paths between these types in `Type`.

```
Path-Sub #(A : Type) (X Y : Sub A) : (X ={Sub A} Y) = (X ={Type} Y) := refl
```

Inductives are a bit more problematic. Usually it's easy to prove a characterization of paths using the encode-decode method, but stating how this will work in general is troublesome.

### Computational properties of negation

Besides `Empty`, `Unit` and `=`, we can also improve our negation.

First, negating `Empty` gives `Unit` and vice versa.

```
not-Empty : ~ Empty = Unit
not-Unit : ~ Unit = Empty
```

But that's not all: now we also need some new computational equalities at the term level.

```
not-Empty' (x : ~ Empty) : x = unit := refl
not-Unit (x : ~ Unit) : x = x unit := refl
```

Negation of most of the primitive types is `Empty`.

```
not-i8  : ~ i8 = Empty := refl
not-i16 : ~ i16 = Empty := refl
not-i32 : ~ i32 = Empty := refl
not-i64 : ~ i64 = Empty := refl

not-u8  : ~ u8 = Empty := refl
not-u16 : ~ u16 = Empty := refl
not-u32 : ~ u32 = Empty := refl
not-u64 : ~ u64 = Empty := refl

not-f32 : ~ f32 = Empty := refl
not-f64 : ~ f64 = Empty := refl

not-Char : ~ Char = Empty := refl
not-Text : ~ Text = Empty := refl
```

The term-level rules are somewhat arbitrary and ad-hoc.

```
not-i8'  (x : ~ i8)  : x = x 0 := refl
not-i16' (x : ~ i16) : x = x 0 := refl
not-i32' (x : ~ i32) : x = x 0 := refl
not-i64' (x : ~ i64) : x = x 0 := refl

not-u8'  (x : ~ u8)  : x = x 0 := refl
not-u16' (x : ~ u16) : x = x 0 := refl
not-u32' (x : ~ u32) : x = x 0 := refl
not-u64' (x : ~ u64) : x = x 0 := refl

not-f32' (x : ~ f32) : x = x 0.0 := refl
not-f64' (x : ~ f64) : x = x 0.0 := refl

not-Char' (x : ~ i8) : x = x '' := refl
not-Text' (x : ~ i8) : x = x "" := refl
```

For arrays, the story is a bit more complicated: the type `Array A n` is uninhabited only when `A` is uninhabited and `n` is not zero. Providing the term-level equation, however, is pretty difficult, so we won't have any equation for a negated `Array`.

Other types for which we won't have any additional computational equalities with respect to negation are function types, path types and nominal function types.

But we will have an additional equation for the type of names - of course negating `Name A` returns `Empty`, since `Name A` is a countable set for any `A`.

```
not-Name : ~ Name A = Empty := refl
not-Name' (x : ~ Name A) : x = anonymize (ν α. x α) := refl
```

The term-level equation is a bit complicated. To get a proof of `Empty` from `x : ~ Name A`, we need to supply `x` with a name. Since we don't have one, we will create it using nominal abstraction. But then we have `ν α. x α : ∇ α. Empty`, so we need to `anonymize` it before we proceed to get a clean proof of `Empty`.

We also won't have any more computational equalities for records and refinement types. But we will have some for sums singletons.

```
not-Sum : ~ (A + B) = ~ A * ~ B := refl
not-Sum' (x : ~ (A + B)) : x = (inl >> x, inr >> x) := refl
```

Negation of a sum is a product of negations. At the term level, we use function composition `>>` to get `~ A` from `inl : A -> A + B` and `x : ~ (A + B)` and similarly for `inr`.

Negating a singleton type of course gives an `Empty`.

```
not-Singleton #(A : Type, x : A) : ~ Singleton A x = Empty := refl
not-Singleton' (s : ~ Singleton A x) : s = s x := refl
```

Negations of universes are `Empty`.

```
not-Type : ~ Type = Empty := refl
not-Type' (x : ~ Type) : x = x Empty := refl

not-hType : ~ hType = Empty := refl
not-hType' (x : ~ hType) : x = x Empty := refl
```

Similarly, because all types have at least one subtype (which is, of course, `Empty`), negating the universe of subtypes of any types gives `Empty`.

```
not-Sub (A : Type) : ~ Sub A = Empty
not-Sub' #(A : Type) (x : ~ Sub A) : x = x Empty
```

We don't have any additional computational equalities for inductive and coinductive types, but if we wanted, we could generalize the equation for sums to one for least fixpoints.

```
~ (μ X. F X) ≡ ν X. ~ (F (~ X))
```

### Summary

Of course we don't want to confine ourselves to just built-in computational equalities for `Empty`, `Unit` and path types (and negation) - we want to be able to define custom types with custom equalities of this kind.

One way to do this is with rewrite rules, which can also be used to realize the additional computational properties we have already seen. The prototype is implemented in Agda. I'm not sure how rewrite rules interact with Agda's `Prop`, but I think this shouldn't be a problem.

Book:
- [Term Rewriting And All That](https://www21.in.tum.de/~nipkow/TRaAT/)

Papers:
- [Type Theory Unchained: Extending Agda with User-Defined Rewrite Rules](https://drops.dagstuhl.de/opus/volltexte/2020/13066/pdf/LIPIcs-TYPES-2019-2.pdf) (see section 2.6 for how to get rewriting rules for ordinary equality - if I read the paper correctly, it's also possible for Path types)
- [The Taming of the Rew: A Type Theory with Computational Assumptions](https://hal.archives-ouvertes.fr/hal-02901011v2/document)
- [The Multiverse: Logical Modularity for Proof Assistants](https://arxiv.org/pdf/2108.10259.pdf)

**Status: very wild speculations.**

TODO:
- Find how these types will be declared.
- Make sure that it all makes sense.
- `unrefine` for refinement types, a pattern for the `Empty` type.
- Maybe we shouldn't get rid of refinements on `Unit` (i.e. by additing more computational equalities)?
- Revisit "paths between paths are squares".
- Write a section on general rewriting in type theory.

# TODO: Missing features <a id="TODO"></a> [↩](#toc)

This wishlist is not comprehensive. We could probably do better (i.e. have more nice things), but we have to stop somewhere, not to mention that all the interactions between all the different features blow up the complexity of the language dramatically.

## List notation for `List`-like types <a id="list-notation"></a> [↩](#toc)

When we defined `List` for the first time, we named the constructors `[]` and `_::_`. These correspond to the usual `Nil` and `Cons`, respectively.

But in most functional languages, we are accustomed to the list syntax being `[1, 2, 3, 4, 5]` (even though the separator may vary). How can we make this syntax available in our language?

Our language is even more ambitious - we want to use this syntax for any listlike type. By "listlike", I mean a type that has a nil and a cons, represented by `Nil` and `Cons`, such that `Nil` means "the end" and `Cons` means "put one more thing at the front". The notation, however it is realized, translates `[]` to `Nil` and `[h, ...]` to `Cons h ...`.

```
l : List Nat := [1, 2, 3, 4, 5]

v : Vector Nat 5 := [1, 2, 3, 4, 5]

q : Queue Nat := [1, 2, 3, 4, 5]

d : Deque Nat := [1, 2, 3, 4, 5]

bv : BitVector 5 := [1, 1, 0, 0, 1]

// Assuming that `G` is a graph in which `e1`, `e2`, `e3`, `e4` and `e5` are
// paths whose sources and targets are compatible.
p : Path G := [e1, e2, e3, e4, e5]
```

Examples of listlike types include not only `List`, but also `Vec` and many more, like queues, deques, sequences, bit vectors, paths in graphs, and so on.

The notation can be realized in a few ways:
- Using a typeclass - we need to define `Nil` and `Cons`. However, it might be hard to come up with a generic interface for listlike types.
- Attach the notation to any (co)inductive types whose constructor are named `Nil` and `Cons`, provided that their types are ok. Again, it might be hard to decide whether `Cons` has the right type or not.
- Make the notation available only for built-in types. This is bad, because we don't want to make lists or vectors built-in.

Papers:
- None.

**Status: speculations.**

TODO:
- Look for some papers.
- Think about it for some more time.

## Singleton Types <a id="singletons"></a> [↩](#toc)

A singleton type is a type that has exactly one value. We can already express this with in our type theory with the following type.

```
Sad-Singleton : RType
& A : Type
& c : A
& p : (x : A) -> c = x
```

The thing is, the above type has exactly one value only up to a path, whereas we want true singleton types to have exactly one value up to computational equality.

When `A : Type` and `x : A`, we can form the type `Singleton A x` (also written `{x}` and more explicitly `{x}_A`) which represents the type whose only value is `x` and which is a strict proposition.

Papers:
- [Subtyping with Singleton Types](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.5.8740&rep=rep1&type=pdf)
- [Singleton types here, Singleton types there, Singleton types everywhere](https://www.iro.umontreal.ca/~monnier/comp-deptypes.pdf)
- [Strong Normalization with Singleton Types](https://www.doc.ic.ac.uk/~svb/ITRS02/ENTCS/entcs75105.pdf)
- [Singleton Kinds and Singleton Types](https://apps.dtic.mil/sti/pdfs/ADA387141.pdf)
- [A Modular Type-checking algorithm for Type Theory with Singleton Types and Proof Irrelevance](https://arxiv.org/pdf/1102.2405.pdf)

**Status: some kind of singleton types are present in Scala and Typescript, and HoTT has "homotopy singletons", but true singleton types in type theory have not been researched.**

TODO:
- Read the papers.
- Write something.

## Generic programming <a id="generic"></a> [↩](#toc)

Generic functions are functions implemented by recursion on the structure of types in the language. For example, we could implement decidable equality for all types that support it all at once.

Less relevant papers:
- [Extensible and Modular Generics for the Masses](http://www.cs.ox.ac.uk/bruno.oliveira/extensibleGM.pdf) - how to do generic programming with typeclasses in Haskell

**Status: generic programming is rare. Haskell can do it using typeclasses and Idris 2 allows typecase, but the prospects are meek.**

TODO:
- Search for papers.
- Read the papers and see how generic programming and typecase fit into the language.
- Write something about typeclasses.

## Quantitative Type Theory <a id="quantities"></a> [↩](#toc)

Papers:
- [I Got Plenty o’ Nuttin’](https://personal.cis.strath.ac.uk/conor.mcbride/PlentyO-CR.pdf)
- [Syntax and Semantics of Quantitative Type Theory](https://bentnib.org/quantitative-type-theory.pdf)
- [Idris 2: Quantitative Type Theory in Practice](https://arxiv.org/pdf/2104.00480.pdf)

Prototypes:
- [Idris 2](https://idris2.readthedocs.io/en/latest/tutorial/index.html)

TODO:
- Read the papers and see if Quantitative Type Theory conflicts with anything else we want to have in the language.

## Graded Modalities <a id="graded-modalities"></a> [↩](#toc)

Papers:
- [A Graded Dependent Type System with a Usage-Aware Semantics (extended version)](https://arxiv.org/pdf/2011.04070.pdf)
- [Graded Modal Dependent Type Theory](https://arxiv.org/pdf/2010.13163.pdf)
- [Combining Effects and Coeffects via Grading](https://cs-people.bu.edu/gaboardi/publication/GaboardiEtAlIicfp16.pdf)
- [Quantitative Program Reasoning with Graded Modal Types](https://metatheorem.org/includes/pubs/ICFP19.pdf)

Prototypes:
- [Granule](https://github.com/granule-project/granule/blob/main/examples/intro.gr.md) (this link leads to a nice intro with actual code)

Tangential papers (on graded monads):
- [Unifying graded and parameterised monads](https://arxiv.org/pdf/2001.10274.pdf)
- [Towards a Formal Theory of Graded Monads](https://www.researchgate.net/publication/309092270_Towards_a_Formal_Theory_of_Graded_Monads)
- [Relational Algebra by Way of Adjunctions](https://dl.acm.org/doi/pdf/10.1145/3236781) ([slides](http://www.cs.ox.ac.uk/jeremy.gibbons/publications/reladj-dbpl.pdf))

TODO:
- Read the tutorial and learn to work with graded modalities.
- Read the paper and see if anything there conflicts with the rest of our language.
- Find out the relationship between graded modalities and Quantitative Type Theory. Idris 2 is nice because structural typing is default and linear typing is optional, whereas Granule seems to have mandatory linear typing. Can anything be done about this?

## Typed Holes <a id="holes"></a> [↩](#toc)

Holes are a way of leaving a part of a term unfilled as a kind of local "axiom". They can be later revisited with the help of the language's type inference, filled automatically or serve as names for goals in the proving mode. More ambitious works try to use holes for accomodating ill-typed, ill-formed and incomplete (yet unwritten) programs into the semantics.

Papers:
- [Live Functional Programming with Typed Holes](https://dl.acm.org/doi/pdf/10.1145/3290327)

TODO:
- Typed Holes have something to do with First-Class Patterns. And what if we could make typed holes first-class?

## Tactics <a id="tactics"></a> [↩](#toc)

## Metaprogramming <a id="meta"></a> [↩](#toc)

## Mixfix operators and notation mechanism <a id="notation"></a>

## Tooling <a id="tooling"></a> [↩](#toc)

[The Unison Language](https://www.unisonweb.org/) has a very futuristic tooling and some good ideas, including:
- Codebases: Unison code is literally stored as an AST in a nice database managed with a dedicated tool
- Everything can be referred to by its hash. Names are just metadata, so it is easy to rename stuff and perform other similar magic like caching tests.