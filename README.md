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
1. [Empty and Unit](#empty-and-unit)
1. [Records (and sums)](#records)
1. [Basic Inductive Types](#basic-inductive-types)
1. [Pattern matching on steroids](#pattern-matching)
    1. [Overlapping and Order-Independent Patterns](#overlapping-patterns)
    1. [Decidable Equality Patterns](#decidable-equality-patterns)
1. [Inductive Families](#inductive-families)
    1. [Standard Inductive Families](#standard-inductive-families)
    1. [Nested Inductive Types](#nested-inductive-types)
    1. [Indices that Compute (TODO)](#indices-that-compute)
1. [Advanced Inductive Types](#advanced-inductive-types)
    1. [Computational Inductive Types](#computational-inductive-types)
    1. [Higher Inductive Types](#HIT)
    1. [Nominal Inductive Types](#nominal-inductive-types)
    1. [Induction-Induction](#induction-induction)
    1. [Induction-Recursion](#induction-recursion)
1. [Basic Coinductive Types](#basic-coinductive-types)
1. ["Positive" Coinductive Types](#positive-coinductive-types)
1. [Coinductive Families](#coinductive-families)
1. [Advanced Coinductive Types](#advanced-coinductive-types)
1. [Refinement types (TODO)](#refinements)
1. [Singleton Types (TODO)](#singletons)
1. [Universes](#universes)
1. [Subtyping, coercions and subtype universes](#subtyping)
1. [Type-level rewriting](#type-level-rewriting)
1. [Tooling (TODO)](#tooling)
1. [Missing features (TODO)](#missing-features)

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
- Invent syntax for documentation comments.
- Documentation is well known for its tendency to go out of sync with the code. So maybe it's time to make it strongly-typed? See [the Unison Language](https://www.unisonweb.org/docs/documentation) for more on typed documentation.

## Types <a id="types"></a> [↩](#toc)

| Name              | Formation        | Introduction     | Elimination      |
| ----------------- | ---------------- | ---------------- | ---------------- |
| Primitive types   | `i8`, `i16`, `i32`, `i64` <br> `u8`, `u16`, `u32`, `u64` <br> `f32`, `f64` <br> `Char` <br> `Text` | literals         | primitive ops    |
| Arrays            | `Array A n`      | literals <br> library functions | `A[i]`     |
| Function type     | `(x : A) -> B x` | `fun x : A => e` | `f a`            |
| Path type         | `x = y`          | `path i => e`    | `p i`            |
| Nominal function type | `∇ α : A. B α`   | `ν α : A. e`     | `t @ α`      |
| Name              | `Name A`         | with `∇` and `ν` | pattern matching |
| Empty type        | `Empty`          | impossible       | `abort`          |
| Unit type         | `Unit`           | `unit`           | not needed       |
| Record types      | `(a : A, ...)`   | `(a => e, ...)`  | `p.x`            |
| Sum types         | not sure         |                  |                  |
| Inductive types   |  see below       | constructors     | pattern matching |
| Coinductive types |  see below       | copattern matching | field selection |
| Refinement types  | `{x : A \| P x}` | implicit (?)     | implicit (?)     |
| Singleton types   | `Singleton A x`  | TODO             | TODO             |
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

**Status: implemented in Coq.**

TODO:
- How does it work at the level of formal rules? Do we need zillion rules for every single primitive operation and its specification?
- Decide the details of the char type.
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

We can omit writing implicit arguments altogether when they are easily inferable from something else. This piece of syntax is inspired by [Idris 2](https://idris2.readthedocs.io/en/latest/tutorial/typesfuns.html#implicit-arguments). We will call it "super implicit arguments". It is used pretty often in this repo, almost always with `A` and `B` standing in for types.

```
id (x : A) : A := x

comp (f : A -> B) (g : B -> C) (x : A) : C := g (f x)
```

There are also other kinds of implicitness, like looking up typeclass instances, but these are dealt with by [records](#records).

Names of functions are allowed to consist entirely of symbols, although this style is discouraged except for the most common functions, like the above operators borrowed from F#: pipe forward `|>`, pipe backward `<|`, forward function composition `>>` and backward function composition `<<`.

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

**Status: prototype implemented for CNIC, but long ago (and with Lisp syntax, lol). Prototype implemented for FreshMLTT, but it looks like shit. No proof whether FreshMLTT has decidable typechecking.**

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

## `Empty` and `Unit` <a id="empty-and-unit"></a> [↩](#toc)

There's the built-in `Empty` type which has no terms in the empty context. It's eliminator is called `abort`.

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

Just like before, we don't need the `open`, because record arguments are opened automatically.

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

### Sums

As for sum types, we would like to have extensible sum types, akin to OCaml's polymorphic variants. If that's not possible, then sum types are subsumed by inductive types. In theory, getting records right should be enough to get sums right, as they are dual to records.

### Summary

[Here](Records/TurboRecords.ttw) you can find a wilder and more ambitious idea of what records should be.

Papers on dependent records in type theory:
- [Dependent Record Types Revisited](http://www.cs.rhul.ac.uk/home/zhaohui/DRT11.pdf)
- [Typed Operational Semantics for Dependent Record Types](http://www.cs.rhul.ac.uk/home/zhaohui/TYPES09final11-01-01.pdf)
- [Ur: Statically-Typed Metaprogramming with Type-Level Record Computation](http://adam.chlipala.net/papers/UrPLDI10/UrPLDI10.pdf)
- [Abstracting Extensible Data Types: Or, Rows by Any Other Name](https://www.pure.ed.ac.uk/ws/portalfiles/portal/87175778/Abstracting_extensible_data_types_MORRIS_DoA_tbc_VoR_CC_BY.pdf)

Older papers:
- [Extension of Martin-Löf 's Type Theory with Record Types and Subtyping](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.49.5862&rep=rep1&type=pdf)
- [Dependently Typed Records in Type Theory](https://sci-hub.se/10.1007/s001650200018) (also see [Agda code](https://agda.github.io/agda-stdlib/Data.Record.html) based on the paper)
- [Dependently Typed Records for Representing Mathematical Structure](https://sci-hub.se/10.1007/3-540-44659-1_29)
- [A Logical Framework with Dependently Typed Records](https://www.researchgate.net/publication/226374245_A_Logical_Framework_with_Dependently_Typed_Records)
- [Algebraic Structures and Dependent Records](https://www.researchgate.net/publication/242555886_Dependent_record_types_and_algebraic_structures_in_type_theory)

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

**Status: mostly wild speculations. The papers promise much, but no good implementations/prototypes, so probably there's something wrong with them. Sums probably won't happen.**

TODO:
- Finish thinking about records.
- How to turn typing contexts into record types? This would free us from some duplication at the meta level. But beware! This is not the same idea as "first-class typing contexts" and certainly not the same as "first-class evaluation contexts".
- Rethink modify syntax for modules.
- Rethink whether the prototype should really go at the end of the record definition.
- Deduplicate explanations of `open` syntax in the first three sections and then in Problem 1 section.
- How exactly do dependent records work? We need more examples.
- Discuss the sort of record types and how to declare record types.
- Discuss implicit record fields.
- How to avoid the ugly `A setting x to x` thing? Maybe `A @x` for passing implicit arguments?
- Rethink whether `$` is a good syntax for record type prototyping. Make sure it does not collide with `$=>` and with `$` used for complex function application.
- Decide whether prototype copatterns should be at the beginning or at the end.
- Rethink `RType` and how to make records first-class.
- Add a term-level `removing` operation.

## Basic Inductive Types <a id="basic-inductive-types"></a> [↩](#toc)

Basic inductive types work mostly as usual, but as for functions, we want to think that all constructors take just one argument which is a (possibly dependent) record.

The different genres of inductive types (enumerations, parameterized types, inductive families, etc.) have progressively more complete syntaxes, so that simple types can be written in a simple way and only the more complicated ones require more details.

Enumerations can NOT be written in a single line and must have the initial bar. Note that we don't need to (and should not) write the return type of the constructors when it's the same in every case.

```
data Bool : Type
| ff
| tt
```

Definition by patterns matching are very concise.

```
notb : Bool -> Bool
| ff => tt
| tt => ff
```

We should name the argument of each constructor, as this will be used for automatic name generation - something well known to be lacking in most proof assistants.

```
data _*_ (A B : Type) : Type
| pair (outl : A) (outr : B)
```

This doesn't affect the ordinary way of doing pattern matching that binds names.

```
swap : A * B -> B * A
| pair x y => pair y x
```

But if we want, we can rely on arguments' original names in definitions by pattern matching.

```
swap : (x : A * B) -> B * A
| pair => pair x.outr x.outl
```

We can also unpack the constructor's arguments in place to use their shorter names by postfixing the constructor's name with `{..}` (this syntax is based on Haskell's [Record Wildcards](https://kodimensional.dev/recordwildcards)).

```
swap : A * B -> B * A
| pair{..} => pair outr outl
```

Even better: we don't need to write `{..}` because records get opened/unpacked automatically.

```
swap : A * B -> B * A
| pair => pair outr outl
```

As usual, the inductive type being defined can appear as argument to any of the constructors, provided that it stands in a strictly positive position.

```
data Nat : Type
| z
| s (pred : Nat)
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
| _::_ (hd : A) (tl : List)
```

This distinction applies both to inductive and recursive definitions. It looks a bit weird at first, as that's not what people are used to, but hey, you are going to appreciate it when the definitions get more complicated!

```
map (f : A -> B) : List A -> List B :=
| []     => []
| h :: t => f h :: map t
```

The distinction between parameters and indices has some other consequences too. For example, when defining additions of naturals, the most succinct definition forces us to do it by recursion on the second argument.

```
add (n : Nat) : Nat -> Nat :=
| z   => n
| s m => s (add m)
```

For functions that are not commutative, like list append, we get a bit more headache, as we need to match two arguments even though we don't use the second one.

```
app : (l1 l2 : List A) -> List A :=
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

The above use of a `with`-clause if equivalent to the following use of an `if-then-else` expression.

```
filter (p : A -> Bool) : List A -> List A
| [] => []
| h :: t => if p h then h :: filter t else filter t
```

### Discriminators

As a slight bonus, when we define an inductive type, we get for free discriminators which check what constructors a term was made with. This feature is inspired by the F* language. They are named after the constructor, with a `?` at the end.

For `Bool`, they are

```
tt? : Bool -> Bool
ff? : Bool -> Bool
```

and for `Nat`, the discriminators are

```
z? : Nat -> Bool
s? : Nat -> Bool
```

Their definitions are very predictable. For example, `z?` is defined as follows.

```
z? : Nat -> Bool
| z => tt
| _ => ff
```

We also have discriminators for `List A`, although their names are somewhat ugly.

```
[]? : List A -> Bool
::? : List A -> Bool
```

### Constructor names and namespacing

Note that constructors of inductive types do NOT need to be globally unique, unlike in many other languages.

```
data TrafficLight
| Red
| Orange
| Green

data Color
| Red
| Green
| Blue
| RGBA (r : u8, g : u8, b : u8, a : u8)
```

Both of the above types have constructors named `Red` and `Green`, but there is no confusion between them. For example, if we apply a function `canDrive : TrafficLight -> Bool` to `Red`, i.e. `canDrive Red`, then `Red` is interpreted as `Red : TrafficLight`. If a color is expected, e.g. in `isPretty Red` for `isPretty : Color -> Bool`, `Red` is interpreted as `Red : Color`.

If we need to disambiguate between the two `Red`s, we can write `TrafficLight.Red` and `Color.Red`, respectively. Here the dot syntax is the same as for records, and in fact every inductive type has its own namespace, which is a record that holds various useful things related to the inductive type, like its constructors or its elimination principle.

Papers:
- [Inductive Types Deconstructed](https://www.iro.umontreal.ca/~monnier/itd-tyde-2019.pdf)
- [Elaborating Inductive Definitions](https://arxiv.org/pdf/1210.6390.pdf)
- [The Gentle Art of Levitation](https://www.irif.fr/~dagand/papers/levitation.pdf)
- [A Cosmology of Datatypes](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.366.3635&rep=rep1&type=pdf)

**Status: inductive types and pattern matching are standard, with Agda probably being the closest implementation to what has been described so far. Discriminators are not standard, but implemented in F\*, so they shouldn't pose a problem. Each inductive type being its own namespace/module is also not standard, but implemented in Lean, so it also shouldn't pose any problems.**

TODO:
- Make sure that `@` used for as-patterns doesn't clash with `@` used for explicit arguments and `@` used for name concretion.
- Describe nested inductive types.
- Describe list notation for list-like types.
- Describe bundled syntax for inductives (and inductive families).

## Pattern matching on steroids <a id="pattern-matching"></a> [↩](#toc)

Besides the usual pattern matching, we also allow some extensions which significantly increase its power:
- [Overlapping and Order-Independent Patterns](#overlapping-and-order-independent-patterns)
- [Decidable Equality Patterns](#decidable-equality-patterns)

### [Overlapping and Order-Independent Patterns](Induction/OverlappingPatterns) <a id="overlapping-patterns"></a> [↩](#toc)

Consider the usual definitions of addition of natural numbers.

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

## Inductive Families <a id="inductive-families"></a> [↩](#toc)

### Standard Inductive Families <a id="standard-inductive-families"></a> [↩](#toc)

For inductive families, we need to explicitly write the constructor's return type (because it depends on the index), but we still don't need to write the parameters.

```
data Vec (A : Type) : Nat -> Type
| Nil  : Vec z
| Cons : (hd : A, #n : Nat, tl : Vec n) -> Vec (s n)
```

When doing dependent pattern matching, the shape of an earlier pattern may be determined by the shape of a later pattern, for example when we are matching on the index on an inductive family and then on an element of this family with that index.

```
head : (#n : Nat, v : Vec (s n)) -> A
| .n', Cons h n' t => h
```

We call these _forced patterns_, contrary to [Agda](https://agda.readthedocs.io/en/v2.5.2/language/function-definitions.html#special-patterns) which calls them _inaccessible patterns_.

Papers:
- [Pattern Matching Without K](https://jesper.sikanda.be/files/pattern-matching-without-K.pdf)
- [A Syntax for Mutual Inductive Families](https://drops.dagstuhl.de/opus/volltexte/2020/12345/pdf/LIPIcs-FSCD-2020-23.pdf)

**Status: inductive families are standard in proof assistants and dependently-typed languages. Dependent pattern matching is semi-standard, as some languages (notably Coq) have problems with supporting it properly so it's hard to use, while some others (Idris 2 and formerly Agda) have implementations of it that entail Uniqueness of Identity Proofs, which is incompatible with Univalence. The closest implementation of what's described here is probably Agda (with the flag `--without-K`).**

### Nested Inductive Types <a id="nested-inductive-types"></a> [↩](#toc)

Nested inductive types are inductive families `I : Type -> Type` in which the inductive occurrences of `I A` are nested in another type family (the first kind of nested inductive types) or in which their indices are nested in another family (the second kind of nested inductive types).

Nested inductives of the first kind can be defined as usual parameterized types. One of the most iconic examples is the type of rose trees, i.e. trees that have a `List` of subtrees.

```
data RoseTree (A : Type)
| E
| N (v : A, ts : List RoseTree)
```

Functions out of such types can be defined as usual by pattern matching and recursion, with the nested recursion (i.e. on the `List` in case of `RoseTree`) being handled just fine.

```
size : RoseTree A -> Nat
| E => 0
| N _ [] => 1
| N v (t :: ts) => size t + size (N v ts)
```

In the above example, we compute the `size` of a `RoseTree`. The interesting constructor, `N`, is split into two cases: if there are no subtrees, we return `1`, whereas if there are, we call `size` recursively on the first subtree `t` and then on on `N v ts`, i.e. on what remains of our original `RoseTree` after we remove the first subtree `t`.

These recursive calls are perfectly legal - `t` is a subterm of `N v (t :: ts)`, so `size t` is a good recursive call. `N v ts` is not a subterm of `N v (t :: ts)`, but it is smaller in an obvious way, and the termination checker sees that.

There are a few other ways to implement `size`.

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
| N _ ts => 1 + sum (map size ts)
```

In the variant above, we use auxiliary functions `map : (A -> B) -> List A -> List B` and `sum : List Nt -> Nat` (implementation not shown). There are no explicit recursive calls - they are hidden in the call `map size`. This use of recursion, called _higher-order recursion_ (because unapplied/partially applied `size` is used as an argument to a higher-order function) is perfectly legal in our language.

```
size : RoseTree A -> Nat
| E => 0
| N _ ts => 1 + List.rec 0 (fun t ts => size t + ts) ts
```

In the last variant above, instead of `sum` and `map` we use the recursor for lists `List.rec : (#A #R : Type, nil : R, cons : A -> R -> R, x : List A) -> R`. The only explicit recursive call, `size t`, occurs under the `fun`. This is also perfectly legal and the termination checker can see it.

Another famous nested type is the following representation of lambda calculus terms.

```
data Lam : Type -> Type
| Var : (#A : Type, n : Nat) -> Lam A
| App : (#A : Type, l r : Lam A) -> Lam A
| Abs : (#A : Type, body : Lam (Option A)) -> Lam A
```

And yet another, arguably the evilest of them all, is the type of bushes.

```
data Bush : Type -> Type
| E : (#A : Type) -> Bush A
| N : (#A : Type, v : A, bs : Bush (Bush A)) -> Bush A
```

Papers:
- [Deep Induction: Induction Rules for (Truly) Nested Types](https://cs.appstate.edu/~johannp/20-fossacs.pdf)
- [Generating Induction Principles for Nested Inductive Types in MetaCoq](https://www.ps.uni-saarland.de/~ullrich/bachelor/thesis.pdf)
- [An induction principle for nested datatypes in intensional type theory](https://www.irit.fr/~Ralph.Matthes/papers/MatthesInductionNestedJFPCUP.pdf)

**Status: implemented in Coq and Agda, but termination checking, autogeneration of elimination principles and support for proofs is lacking.**

TODO:
- All.

### [Indices that Compute](Induction/IndicesThatCompute) <a id="indices-that-compute"></a> [↩](#toc)

We use the name "Indices that Compute" for a suite of ideas centered around an alternative syntax for inductive families and the idea that it would be good to "merge" recursive and inductive definitions of type families. To make this more precise, consider the two below definitions of what it means for a natural number to be even.

```
data Even : Nat -> Prop
| Even-z  : Even z
| Even-ss (#n : Nat, e : Even n) : Even (s (s n))
```

The first definition is a predicate defined as an inductive family. It effectively says that `z` (zero) is even and that if `n` is even, then `s (s n)` (2 + n) is also even. What are the pros and cons of this definition?

Pros:
- we can pattern match on it
- induction principle (in a Coq-like language)
- irrelevance - as we will see later, thanks to `Prop`, any `e1, e2 : Even n` can be proven equal using just `refl`exivity

Cons:
- quadratic proof size if there is no sharing of the implicit `n`s between constructors
- need to implement the decision procedure manually
- hard to prove that 1 is not even - we need a tactic like Coq's `inversion`, or some boilerplate, or very well-implemented dependent patern matching
- no uniqueness principle - if the codomain wasn't `Prop`, we would need to prove manually that all `e1, e2 : Even n` are equal

```
Even : Nat -> Prop
| z       => Unit
| s z     => Empty
| s (s n) => Even n
```

The second definition is recursive. It says that zero is even, one is not even, and that 2 + n is even when n is. What are the pros and cons of this definition?

Pros:
- constant proof size
- very easy to prove that 1 is not even - `Even (s z)` computes to `Empty`, so the proof of `Even 1 -> Empty` is the identity function
- irrelevance
- uniqueness principle - even if the codomain wasn't `Prop`, all `e : Even n` compute to the same type when `n` is known

Cons:
- can't pattern match on the proof, only on the argument
- need to implement the decision procedure manually
- no induction principle (again, if we're hanging in Coq's vicinity)
- non-standard shape of recursion (i.e. different from what appears in `Nat`'s definition)

The idea behind the name "Indices that Compute" is to merge both of these definitiosn into one, better.

```
data EVEN : Nat -> Prop
| z       => EVEN-z : EVEN z
| s (s n) => EVEN-ss (e : EVEN n) : EVEN (s (s n))
```

This definition is similar to the second definition of `Even` in that it is a definition by pattern matching on the index `n`. However, the pattern matching is not exhaustive, because we omitted the case for `s z`. This means that `EVEN (s z)` will compute to `Empty`. The definition is also similar to the first definition of `Even` in that it provides two constructors, one for proving that `z` is even and the other for proving that `s (s n)` is even if `n` is.

Pros:
- constant proof size
- easy to prove that 1 is not even
- it computes
- induction principle

Cons:
- need to manually implement decision procedure

Q: Can we do anything nice with this?

A: in such a banal case as parity of naturals probably not, but in more complicated ones I think so! Example: matching a regular expression against a string. This can't be easily implemented by recursion, so induction is needed. But even though we use induction, it would be nice if some cases of the definition could compute/simplify to help us a bit.

There's also an alternative way for easy predicates like "being an even number", namely: just implement the decision procedure and declare `(= true)` as a coercion. With special computation rules `Empty`, `Unit` and `=`, this should be more than enough.

```
even : Nat -> Bool
| z       => tt
| s z     => ff
| s (s n) => even n

Bool-to-Prop : Bool -> Prop
| tt => Unit
| ff => Empty
```

Pros:
- constant proof size
- it is its own decision procedure
- easy to prove that 1 is not even
- to sum up: it computes

Cons:
- nonstandard shape of recursion

Note: induction principles may be problematic in Coq or other languages where pattern matching is equivalent to eliminators, but after some thinking, using an induction principle of a type or function (functional induction) in a proof just amounts to copying that type's constructors/functions cases and pasting them in the proof.

Papers:
- [Vectors are records, too](https://jesper.sikanda.be/files/vectors-are-records-too.pdf) (also see [the slides](https://jesper.sikanda.be/files/TYPES2018-presentation.pdf))
- [A simpler encoding of indexed types](https://arxiv.org/pdf/2103.15408.pdf)

**Status: very wild speculations.**

TODO:
- Think about this more.
- Figure out what nonstandard techniques are allowed by having [manifest fields in constructors](Induction/IndicesThatCompute/IndicesThatCompute.ttw).

## [Advanced Inductive Types](Induction) <a id="advanced-inductive-types"></a> [↩](#toc)

Inductive families are just the tip of the iceberg, as our inductive types are supposed to be REALLY powerful. We take the usual inductive families as baseline and add:
- [Computational Inductive Types](#computational-inductive-types)
- [Higher Inductive Types](#higher-inductive-types)
- [Nominal Inductive Types](#nominal-inductive-types)
- [Induction-Induction](#induction-induction)
- [Induction-Recursion](#induction-recursion)

We have listed the various enhancements in order from most to least wild. We take the former ones for granted when describing the latter, so as to show their synergy.

### [Computational Inductive Types](Induction/ComputationalInductiveTypes) <a id="computational-inductive-types"></a> [↩](#toc)

The basic idea here is that in inductive type definitions constructors can pattern match on their arguments and compute (almost) like ordinary recursive functions. Let's see an example.

```
data Z : Type
| z
| s (pred : Z)
  | p k => k
| p (succ : Z)
  | s k => k
```

The above is a definition of the type of integers `Z` with three constructors: `z` - zero, `s`- successor, `p` - predecessor. Using ordinary inductive types this is not a good definition, because it does not represent the integers - there are terms like `s (p z)` which do not correspond to numbers. But in the above definition the constructors `s` and `p` have associated computation rules, which say that `s (p k)` computes to `k` (this is the rule for `s`) and that `p (s k)` computes to `k` (this is the rule for `p`). This means that the only legal closed normal form terms of type `Z` are `z`, finitely many `s`s applied to `z` and finitely many `p`s applied to `z`. Therefore `Z` is a good representation of the integers.

Note that the patterns allowed for constructors' computation rules are using first-match semantics, but that may change in the future.

```
abs : Z -> Z
| z   => z
| s k => s k
| p k => s (abs k)
```

We can define functions using pattern matching and structural recursion, just like for ordinary inductive types. We only need to handle patterns that correspond to closed terms in normal form - terms that will be "computed away" by constructors' computation rules need not (and cannot) be handled. For `Z` this means that we need to handle `z`, `s k` and `p k`, but we must not handle `s (p k)` or `p (s k)`, and optionally we may separately handle `s z`, `p z` etc.

In the above example we want to compute the absolute value of the argument. For non-negative integers this is easy and we just return the argument, whereas for negative numbers we need to recursively turn predecessors into successors.

See [this file](Induction/ComputationalInductiveTypes/Z.ttw) for a more thorough explanation and exploration of the type of integers defined using Computational Inductive Types.

Papers:
- ~~None, this idea is brand new invention of mine.~~
- It turns out that the idea of Computational Inductive Types was invented almost 40 years ago in the language Miranda: [Laws in Miranda](https://sci-hub.se/https://doi.org/10.1145/319838.319839)

**Status: highly experimental. It looks like if we put reasonable constraints on the kinds of computation rules associated with constructors, there isn't any abvious contradiction, nontermination or anything like that. However, there are no prototypes and no papers, except that some Computational Inductive Types can be simulated using [Self Types](https://github.com/uwu-tech/Kind/blob/master/blog/1-beyond-inductive-datatypes.md).**

TODO:
- Come up with more examples of useful Computational Inductive Types.

### [Higher Inductive Types](Induction/HIT) <a id="HIT"></a> [↩](#toc)

Higher Inductive Types are inductive types which can be defined using not only point ("ordinary") constructors, but also path constructors which put additional paths into the type. This has two serious uses: the more practical one is for making all kinds of quotients and quotient-like types (and a lot of these can't be made using Computational Inductive Types, because there is no canonical form of some collection of terms) and the more theoretical one is synthetic homotopy theory.

```
data Set (A : Type) : Type
| in (x : A)
| id
| union (x y : Set A)
  | id, y  => y
  | x , id => x
  | union x y, z => union x (union y z)
| comm (x y : Set A) with (i : I)
  | i0 => union x y
  | i1 => union y x
| idem (x : Set A) with (i : I)
  | i0 => union x x
  | i1 => x
| isSet (x y : Set A) (p q : x = y) (i j : I) with i
  | i0 => p j
  | i1 => q j
```

Consider this higher-inductive definition of a set, in the sense of a collection of things of type `A`. This type has three point constructors (including one with additional computation rules) and three path constructors (including a two-dimensional one).

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

**Status: prototype implementations include [cubicaltt](https://github.com/mortberg/cubicaltt), [Cubical Agda](https://agda.readthedocs.io/en/v2.6.0/language/cubical.html), [Arend](https://arend-lang.github.io/) and some other minor languages. No general syntax for HITs is known. Various papers describe subclasses of HITs or HITs combined with induction-induction or something like that. Probably it's very easy to get the most basic and useful HITs, but very hard to get all of them right.**

### [Nominal Inductive Types](Induction/NominalInductiveTypes/CNIC) <a id="nominal-inductive-types"></a> [↩](#toc)

The basics of names and nominal function types are described [here](#names). In this section we only describe how to use nominal features in combination with inductive types to define syntaxes of languages, logics and calculi.

```
data Term : Type
| Var (x : Name Term)
| App (l r : Term)
| Lam (t : ∇ α : Term. Term)
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

### [Induction-Induction](Induction/Induction-Induction) <a id="induction-induction"></a> [↩](#toc)

Induction-induction allows us to simultaneously define two or more types such that the later ones can be indexed by the earlier ones.

```
data Dense (R : A -> A -> Prop) : Type
| in   (x : A)
| mid #(x y : Dense) (H : Dense-R R x y)
| eq  #(x   : Dense) (H : Dense-R R x x) with (i : I)
  | i0 => mid x x H
  | i1 => in x

with Dense-R (R : A -> A -> Prop) : Dense R -> Dense R -> Prop
| in   : #(x y : A) (H : R x y) -> Dense-R (in x) (in y)
| midl : #(x y : Dense R) (H : Dense-R x y) -> Dense-R (mid x y H) y
| midr : #(x y : Dense R) (H : Dense-R x y) -> Dense-R x (mid x y H)
```

In the above example, `Dense-R R` is the dense completion of its parameter relation `R`, which means that it represents the least dense relation that contains `R`. `Dense-R` is defined at the same time as `Dense`, which represents its carrier - the type `A` with added midpoints of all pairs `x, y` such that `R x y`.

Note that the constructors of `Dense` refer to `Dense-R`, the constructors of `Dense-R` refer to constructors of `Dense`, and the indices of `Dense-R` refer to `Dense`. This is characteristic of induction-induction. Also note that `eq` is a path constructor - we may freely mix inductive-inductive types with higher inductive types.

```
data BHeap (R : A -> A -> Prop) : Type
| E
| N (v : A, l r : BHeap R, okl : OK R v l, okr : OK R v r)

and OK (R : A -> A -> Prop) (v : A) : BHeap R -> Prop
| OK-E : OK E
| OK-N : (x : A) (l r : BHeap R) -> R v x -> OK (N x l r)
```

Another classic use of induction-induction is to define data structures with non-trivial invariants. Above, we define the type of binary heaps (ordered by the relation `R`), which can be either `E`mpty, or consist of a `N`ode that holds a `v`alue and two subheaps `l` and `r`, which are `OK`, i.e. satisfy the (one-layer, non-recursive) heap condition, which holds for empty heaps and for nodes whose value is smaller than the values in their subheaps.

Binary heaps could be easily defined even without induction-induction, by first defining binary trees inductively, then the heap condition as an inductive family and finally by putting them together in a dependent record and lifting all binary tree operations to binary heaps. Note, however, that an inductive-inductive definition is so much simpler and more elegant.

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

### [Induction-Recursion](Induction/Induction-Recursion) <a id="induction-recursion"></a> [↩](#toc)

Induction-Recursion is an enhancement of inductive types which allows us to mutually define an inductive type `I` and a recursive function of type `I -> D` for some type `D`. There are two common use cases:
- Large induction-recursion: here `D` is `Type`. This flavour of induction-recursion is used for defining closed universes of types.
- Small induction-recursion: here `D` is something  other than `Type`. This flavour of induction-recursion is used for defining data types in a manner similar to induction-induction, but with more computational niceties.

```
data U : Type
| 0
| 1
| + (u1 u2 : U)
| * (u1 u2 : U)
| → (u1 u2 : U)
| pi (dom : U) (cod : El dom -> U)
| eq (u : U) (x y : El u)

and El : (u : U) -> Type
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
| + (u1 u2 : U)
  | 0, u => u
  | u, 0 => u
  | u1 + u2, u3 => u1 + (u2 + u3)
| * (u1 u2 : U)
  | 0, _ => 0
  | _, 0 => 0
  | 1, u => u
  | u, 1 => u
  | u1 * u2, u3 => u1 * (u2 * u3)
  | u1, u2 + u3 => (u1 * u2) + (u1 * u3)
  | u1 + u2, u3 => (u1 * u3) + (u2 * u3)
| → (u1 u2 : U)
  | _, 1 => 1
  | 0, _ => 1
  | 1, u => u
  | u1 * u2, u3 => u1 → (u2 → u3)
  | u1 + u2, u3 => (u1 → u3) * (u2 → u3)
  | u1, u2 * u3 => (u1 → u2) * (u1 → u3)
| pi (dom : U) (cod : El dom -> U)
  | 0, _ => 1
  | 1, _ => cod unit
  | u1 * u2, _ => pi u1 (fun x => pi u2 (fun y => cod (x, y)))
  | u1 + u2, _ => pi u1 (fun x => dom (inl x)) * pi u2 (fun y => dom (inr y))
| eq (u : U) (x y : El u)
  | 0     , _       , _        => Unit
  | 1     , _       , _        => Unit
  | u + v , inl x'  , inl y'   => eq u x' y'
  | u + v , inr x'  , inr y'   => eq v x' y'
  | u + v , _       , _        => Empty
  | u * v , (x1, y1), (x2, y2) => eq u x1 x2 * eq v y1 y2
  | u → v , f       , g        => pi u1 (fun x : El u1 => eq u2 (f x) (g x))
  | pi u v, f       , g        => pi u (fun x : El u => eq v (f x) (g x))

and El : (u : U) -> Type
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
| N (v : A, l r : BHeap R, okl : OK R v l, okr : OK R v r)

and OK (R : A -> A -> Prop) (v : A) : (h : BHeap R) -> Prop
| E => Unit
| N => R v h.v
```

Induction-Recursion, just like induction-induction, can also be used to define data structures with complex invariants. Above we have the binary heaps again, but this time the (non-recursive) heap condition is defined by pattern matching mutually with the type of binary heaps.

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
- [Simulating Induction-Recursion for Partial Algorithms](https://members.loria.fr/DLarchey/files/papers/TYPES_2018_paper_19.pdf) - how to define complicated recursive functions without resorting to induction-recursion)
- [A polymorphic representation of induction-recursion](https://www.researchgate.net/publication/244448805_A_polymorphic_representation_of_induction-recursion) ([slides](http://www.cs.ru.nl/dtp11/slides/capretta.pdf))
- [A Formalisation of a Dependently Typed Language as an Inductive-Recursive Family](https://www.cse.chalmers.se/~nad/publications/danielsson-types2006.pdf)

Generic programming using (inductive-recursive) universes:
- [Fully Generic Programming Over Closed Universes of Inductive-Recursive Types](https://pdxscholar.library.pdx.edu/cgi/viewcontent.cgi?article=4656&context=open_access_etds) - generic programming with universes
- [Generic functional programming](https://gitlab.inria.fr/fpottier/mpri-2.4-public/blob/8485cc50346803d661e1ea4c5b8e485ccad18f66/agda/04-generic/Desc.lagda.rst)

**Status: induction-recursion is implemented in Agda and in Idris 1 (or at least this is what Wiki claims), and there was an experimental branch of Coq that implemented it a long time ago. In general, however, it is not mainstream. Implementation should not be problematic.**

## [Basic Coinductive Types](Coinduction) <a id="basic-coinductive-types"></a> [↩](#toc)

Coinductive types are "negative", i.e. they are record-like types which are defined by specifying what fields they have. Definitions of coinductive types start with the keyword `codata`. Then, in separate lines starting with `&`, we list field names and their types. Below we define a coinductive product type whose left projection is `l` and right projection is `r`.

```
codata _*_ (A B : Type) : Type
& l : A
& r : B
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
& hd : A
& tl : Stream
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

### Field names and namespacing

Note that names of fields do NOT need be globally unique, contrary to what is the case in many other languages.

```
codata NonEmptyCoList (A : Type)
& hd : A
& tl : Option NonEmptyCoList
```

The above type defines a colist, i.e. something like a list, but possibly infinite, which in addition can not be empty. The fields are named `hd` and `tl`, just the fields of `Stream`, but this does not produce much confusion. When accessing a field, like `s.hd`, it is clear from the type of `s` which `hd` is meant. This is the case also in many other situations. If `hd` is truly ambiguous, we can disambiguate by writing `Stream.hd` and `NonEmptyCoList.hd`, respectively. Just like for inductive types, each coinductive type has its own namespace, which is a record that contains the fields in function form (`Stream.hd : (#A : Type, s : Stream A) -> A`) and other useful autogenerated stuff.

Papers:
- [Copatterns Programming Infinite Structures by Observations](https://www.researchgate.net/profile/Anton-Setzer/publication/262366004_Copatterns_Programming_Infinite_Structures_by_Observations/links/587fe0f208ae9275d4ee3ae2/Copatterns-Programming-Infinite-Structures-by-Observations.pdf)
- [Unnesting of Copatterns](http://www2.tcs.ifi.lmu.de/~abel/rtatlca14.pdf)
- [Wellfounded Recursion with Copatterns and Sized Types](http://www2.tcs.ifi.lmu.de/~abel/jfp15.pdf)
- [Elaborating dependent (co)pattern matching](https://jesper.sikanda.be/files/elaborating-dependent-copattern-matching.pdf)
- [Copattern matching and first-class observations in OCaml, with a macro](https://hal.inria.fr/hal-01653261/document)

Not papers:
- [Pattern and Copattern matching](http://www1.maths.leeds.ac.uk/pure/logic/images/slidesLeedsLogicSeminarMay2015.pdf)

**Status: negative inductive types are imeplemented in Agda and Coq. Additionally, copattern matching is implemented in Agda. The Agda implementation of copatterns is based on one of the papers, which means things look pretty good. Name resolution and namespacing is not standard, but probably easy to implement.**

TODO:
- Maybe if we start with patterns, then the definition should still be interpreted as legal corecursive definition?
- Invent Overlapping and Order-Independent Copatterns.
- Another possibility for handling coinductives is for them to be just (co)recursive records, but this depends on how cool and strange records will be.

## "Positive" Coinductive Types <a id="positive-coinductive-types"></a> [↩](#toc)

We have special syntax for coinductive types that have only a single field, like coinductive lists, conatural numbers and so on.

```
codata CoList (A : Type) : Type
| CoNil
| CoCons (hd : A, tl : CoList)
```

The above is neither an inductive type nor a "positive" coinductive type. It is just a syntax sugar that desugars to the following ordinary coinductive type definition.

```
data CoListX (X A : Type) : Type
| CoNilX
| CoConsX (hd : A, tl : X)

codata CoList (A : Type) : Type
& Out : CoListX CoList A

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

### Discriminators and namespaces

Our "positive" coinductive types have their own namespaces, like ordinary inductive and coinductive types. Just like for inductive types, for every "positive" coinductive type we get for free a bunch of discriminators that allow us to check which constructor a value was made with. For `CoList`, these are

```
CoNil?  : CoList A -> Bool
CoCons? : CoList A -> Bool
```

which could be manually implemented as

```
CoNil? : CoList A -> Bool
| Nil    => ff
| CoCons => tt
```

We can find these discriminators in the `CoList`s associated namespace - their full names are `CoList.CoNil?` and `CoList.CoCons?`.

**Status: somewhat experimental. There are no papers nor a prototype implementation. However, it looks pretty reasonable and I have some Coq code [here](Coinduction/Code/Vec.v) that shows an example manual desugaring.**

TODO:
- Write some (pseudo)code that uses this to get comfortable with it.

## Coinductive families <a id="coinductive-families"> [↩](#toc)

The syntax for coinductive families is somewhat similar to that for inductive families - parameters always stay the same and we must omit them, whereas indices change and we must write them explicitly. Contrary to inductive families, we must also name the indices, because that's the only way to refer to them.

As an example, we define a predicate which asserts that the elements of the stream `s` appear in increasing order, where the order relation is represented by the parameter `R`.

```
codata Linked (R : A -> A -> Prop) : (s : Stream A) -> Prop
& link  : R s.hd s.tl.hd
& links : Linked s.tl
```

It's not hard to define the stream of natural numbers starting from `n` and prove that it is `Linked` by `<=`, the standard order on naturals (not defined in the listing). As long as we don't have any fields which are equality proofs, coinductive families are probably easier to use than inductive families.

```
nats (n : Nat) : Stream Nat
& hd => n
& tl => nats (s n)

Linked-nats : (n : nat) -> Linked (<=) (nats n)
& link  => le-n-sn // Easy lemma, we won't prove it.
& links => Linked-nats (s n)
```

The syntax sugar for "positive" coinductive types also works for "positive" coinductive families. Below we define the type of conatural numbers, which are like the natural numbers, but possibly infinite. Then we define the family of "covectors", which are like vectors but possibly infinite and they are indexed by conaturals instead of naturals.

```
codata Conat : Type
| z
| s (pred : Conat)

codata CoVec (A : Type) : Conat -> Type
| CoNil  : CoVec z
| CoCons : (hd : A, #c : Conat, tl : CoVec c) -> CoVec (s c)
```

The whole thing desugars as follows.

```
data ConatX (X : Type) : Type
| zX
| sX (x : X)

codata Conat : Type
& out : ConatX Conat

z : Conat
& out => zX

s (n : Conat) : Conat
& out => sX n

data CoVecF (F : Conat -> Type) (A : Type) : Conat -> Type
| CoNilF : CoVecF z
| CoConsF (h : A, #c : Conat, t : F c) : CoVecF (s c)

codata CoVec (A : Type) (c : Conat) : Type
& out : CoVecF (CoVec A) A c
```

Papers:
- [Elaborating dependent (co)pattern matching](https://dl.acm.org/doi/10.1145/3236770)

**Status: coinductive families are standard, even if people don't always realize this (they look nothing like inductive families).**

## Advanced Coinductive Types <a id="advanced-coinductive-types"></a> [↩](#toc)

There are quite a few flavours of advanced coinductive types:
- Mixed coinductive and inductive types
- Coinduction-Coinduction (analogous to induction-induction) using the "positive" coinductive syntax sugar
- Self-referential types in which some occurrences are inductive and others are coinductive
- Oh man, this is so hard to systematize.

### Coinduction-Recursion? Not really.

Let's try to use induction-recursion syntax together with the `codata` keyword and see what happens. For exploration purposes, we will try to define a type of infinite binary heaps.

```
codata BHeap (R : A -> A -> Prop) : Type
| E
| N (v : A, l r : BHeap, okl : OK v l, okr : OK v r)

and OK #(R : A -> A -> Prop) (v : A) : (h : BHeap R) -> Prop
| E => Unit
| N => R v h.v
```

Aaaaand that's it. The definition looks pretty correct - it's copy-pasted from the earlier inductive-recursive definition of binary heaps, so it probably represents some kind of binary heaps. The only difference is the use of the `codata` keyword. Let's see how to desugar this.

```
data BHeapX (X : Type) (R : A -> A -> Prop) : Type
| E
| N (v : A, l r : X, okl : OKX v l, okr : OKX v r)

and OKX #(X : Type) #(R : A -> A -> Prop) (v : A) : (h : BHeapX X R) -> Prop
| E => Unit
| N => R v h.v

codata BHeap (R : A -> A -> Type) : Type
& Out : BHeapX (BHeap R) R

OK #(R : A -> A -> Prop) (v : A) : (h : BHeap R) -> Prop :=
  OKX v h.Out
```

The desugaring is pretty self-explanatory. We define `BHeapX` and `OKX` by induction-recursion and then tie the knot by defining `BHeap` coinductively as the fixpoint of `BHeap` and `OK` as a wrapper around `OKX`.

The limits of "positive" coinduction-recursion seem to be pretty clear: we can mutually define dependent types coinductively and **non-recursive** functions by pattern matching. Recursive functions, however, are not allowed, because the inductive part of our desugaring is non-recursive, i.e. it is only one layer deep. Therefore, recursion is illegal in this case. This shouldn't be surprising - after all, defining recursive function by pattern matching on a coinductive argument is very illegal.

To sum up: there's no coinduction-recursion, but we can mutually define types coinductively and functions by pattern matching.

### Coinduction-Coinduction? Not really.

What about "coinduction-coinduction" or something like that? Is it possible? Let's find out by defining infinite binary heaps again, but using only induction-induction syntax.

```
codata BHeap (R : A -> A -> Prop) : Type
| E
| N (v : A, l r : BHeap, okl : OK v l, okr : OK v r)

and OK (R : A -> A -> Prop) (v : A) : BHeap R -> Prop
| OK-E : OK E
| OK-N : (x : A) (l r : BHeap R) -> R v x -> OK (N x l r)
```

This definition too is a modification of the original inductive-inductive definition of finite binary heaps, so it's probably correct. The only difference is the use of the `codata` keyword. This desugars as follows.

```
data BHeapX (X : Type) (R : A -> A -> Prop) : Type
| E
| N (v : A, l r : X, okl : OKX v l, okr : OKX v r)

and OKX #(X : Type) #(R : A -> A -> Prop) (v : A) : BHeapX X R -> Prop
| OKX-E : OKX E
| OKX-N : (x : A) (l r : BHeapX X R) -> R v x -> OKX (N x l r)

codata BHeap (R : A -> A -> Type) : Type
& Out : BHeapX (BHeap R) R

OK #(X : Type) #(R : A -> A -> Type) (v : A) (h : BHeap R) : Prop :=
  OKX v h.Out
```

Again, the desugaring looks pretty easy to grasp. `BHeapX` and `OKX` are defined by induction-induction, which is perfectly legal, even though there isn't a lot of induction going on and we could have used ordinary inductive families. Finally, we define `BHeap` by tying the knot and implement `OK` as a wrapper around `OKX`.

From this example it is obvious that there really isn't any coinduction-coinduction going on - it depicts only coinduction-induction, and the "induction" part isn't really that much inductive, as its only one layer deep. But contrary to what was the case for "coinduction-recursion", I don't see why the inductive part of a coinductive-inductive definition couldn't be truly inductive. Maybe we should look for a better example. Also, coinduction-coinduction still seems possible, at least when both types are "positive" coinductives.

### Coinduction-Induction? Somewhat.

The classical example of a mixed coinductive-inductive type is the type of stream processors `SP A B`. It is a more concrete (even though still higher-order) representation of functions of type `Stream A -> Stream B`. The main purpose of it is to define stream processing functions which might not be accepted by the productivity checker.

```
mutual
  codata SP (A B : Type) : Type
  | Put (hd : B, tl : SP A B)
  | Get (gsp : A -> GetSP A B)

  data GetSP (A B : Type) : Type
  | Put (hd : B, tl : SP A B)
  | Get (g : A -> GetSP A B)
```

The implementation is somewhat mysterious, so let's go over it in detail.

The type `SP A B` is the type of stream processors. It is defined coinductively (using our "positive" coinductive syntax sugar), because it is supposed to represent the "output part" of a stream processing function. Since the output is a stream, and streams are coinductive, `SP A B` is also coinductive.

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
| Put' (hd : B, tl : X)
| Get' (gsp : A -> Y)

data GetSP' (X A B : Type) : Type
| In (in : SP' X (GetSP' X A B) A B)

codata SP (A B : Type) : Type
& Out : SP' (SP A B) (GetSP' (SP A B) A B) A B

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

Since both `SP` and `GetSP` have the same base functor (or more poetically, the same "skeleton"), we don't need to duplicate it. Then we tie the know twice, first inductively to obtain an early version of `GetSP` and then coinductively to obtain `SP`. Then we define the final version of `GetSP` and smart constructors that wrap the actual constructors in `In` and `Out`. The desugaring of `toStream` and `toStream'` is somewhat ad hoc and chaotic. It looks more akin to our original definition (the one that used `head` and `tail`) and I wouldn't be very surprised if I made an error here or there...

### Summary

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

**Status: mostly speculation, but based on the solid "positive" coinductive syntax sugar and solid principles. It looks mostly doable.**

TODO:
- Does `let` and copattern matching play out together as nicely as in the last example?
- Reconsider the `mutual` keyword for mutual coinductive-inductive definitions.
- Special syntax for (co)inductive types in which some recursive arguments are to be interpreted inductively and others coinductively.
- Untangleable coinduction-induction?
- Untangleable coinduction-coinduction?

## Refinement types <a id="refinements"></a> [↩](#toc)

The idea is to have, for every type `A`, the type `{x : A | P}` where `P` is some decidable strict proposition that the typechecker (or some external SMT solver, but that's meh...) can reason about. The pioneer in this space is [the F* language](https://www.fstar-lang.org/).

Some nice features related to refinement types that make life a lot easier are the already-described discriminators for inductive (and "positive" coinductive) types.

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

For lists, the projection are

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
- [A MODULAR TYPE-CHECKING ALGORITHM FOR TYPE THEORY WITH SINGLETON TYPES AND PROOF IRRELEVANCE](https://arxiv.org/pdf/1102.2405.pdf)

**Status: TODO**

TODO:
- TODO

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
| Singletons       | `Singleton x : Contr` |
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
| sq (x : A)

// Strict truncation.
%Truncated
data ||_|| (A : Type) : Prop
| |_| (x : A)

// Also pretty useful one: strict set truncation.
%Truncated
data SetSquash (A : Type) : Set
| in (x : A)
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
| s (pred : SNat)

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
| Ess (#n : SNat) (e : Even n) : Even (s (s n))

// Illegal?
data Even : SNat -> Type
| Ez  : Even z
| Ess (#n : SNat) (e : Even n) : Even (s (s n))

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

I have no idea what I'm doing. If something is not described here, it defaults to how it works in [Arend](https://arend-lang.github.io/about/arend-features#universe-levels)

Some reading on universes:
- [Definitional Proof-Irrelevance without K](https://hal.inria.fr/hal-01859964v2/document)
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

**Status: Universe cumulativity is semi-standard, as some proof assistants don't have it. Subtyping for records is standard in the languages that have "structural" record types. Subtyping of anything else in type theory is mostly wild speculations.**

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
| Injection subtyping for sums | `a : A <: [a :> A]` | Note: this only works if the coonstructor is declared as a coercion constructor |
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
data Answer
| Yes
| No

data Option (A : Type)
| Yes (value : A)
| No

data Decision (P : Type)
| Yes (yes : P)
| No  (no  : ~ P)
```

Consider the above definitions of `Answer`, `Option` and `Decision`. `Answer` is a renamed version of `Bool`, with `Yes` instead of `tt` and `No` instead of `ff`. `Option` is defined as usual in ML languages and represents the presence of a `value` (`Yes value`) or lack of a value (`No`). `Decision P` is an analogue of Coq's `sumbool` and represents a decision procedure for the proposition `P`, where the `Yes` constructor carries a proof of `P` and the `No` constructor carries a proof of `~ P`.

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

We should have subtyping between an inductive type and a "positive" coinductive type with the same base functor. For example, `List A` should be a subtype of `CoList A`, where

```
data List (A : Type)
| Nil
| Cons (hd : A, tl : List)

codata CoList (A : Type)
| Nil
| Cons (hd : A, tl : CoList)
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
data Nat
| Z
| S (pred : Nat)

codata Conat
| Z
| S (pred : Conat)
```

with the coercion being

```
%Coercion
c : Nat -> Conat
| Z   => Z
| S n => S (c n)
```

**Status: very speculative, but looks easy to implement provided that basic subtyping already works.**

### Subtyping between negative and "positive" coinductive types

"Positive" coinductive types often represent data structures that are potentially infinite, whereas negative coinductive types often represent versions of these data structures that are necessarily infinite (for completeness, inductives represent versions of these data structures that are necessarily finite).

For example, `Stream`s are necessarily infinite, whereas `CoList`s are only potentially infinite (and `List`s are necessarily finite). Therefore it makes sense to ask whether there can be some subtyping between `Stream A` and `CoList A`. Certainly we can define a function `c : Stream A -> CoList A` and declare it a coercion, but having to do this every single time and for every pair of types would force us to write a lot of boilerplate.

We propose a different solution of this problem: we can declare a constructor name for negative coinductive types. This name is then used to determine subtyping relations for the type.

```
codata Stream (A : Type)
& constructor Cons
& hd : A
& tl : Stream

codata CoList (A : Type)
| Nil
| Cons (hd : A, tl : CoList)
```

The type family `Stream` defined as above is equivalent to our previous definition, but additionally we get an autogenerated function `Cons : (hd : A, tl : Stream A) -> Stream A`, so that we can write `Cons h t` and we need to use neither tuple syntax (`(hd => h, tl => t)`) nor copattern syntax nor module syntax.

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
data List (A : Type)
| Nil
| Cons (hd : A, tl : List)

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
codata Covec (A : Type) : Conat -> Type
| Nil  : Vec z
| Cons : (hd : A, #n : Conat, tl : Covec n) -> Covec (s n)
```

Because `Nat <: Conat` and the constructor names (and constructors' fields' names) match, we have an autogenerated coercion `c : Vec A n <: Covec A n` (or more precisely `c : Vec A n <: Covec A (c' n)`, where `c' : Nat <: Conat`). This coercion could be manually implemented as

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
| s (pred : Z)
| p (succ : Z)
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
data ConsList (A : Type)
| Nil
| Cons (hd : A, tl : ConsList)

data BiList (A : Type)
| Nil
| Cons (hd : A, tl : BiList)
| Snoc (init : BiList, last : A)
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
data SnocList (A : Type)
| Nil
| Snoc (init : SnocList, last : A)
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

Negation of a sum if a product of negations. At the term level, we use function composition `>>` to get `~ A` from `inl : A -> A + B` and `x : ~ (A + B)` and similarly for `inr`.

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

## Tooling <a id="tooling"></a> [↩](#toc)

[The Unison Language](https://www.unisonweb.org/) has a very futuristic tooling and some good ideas, including:
- codebases - Unison code is literraly stored as an AST in a nice database managed with a dedicated tool
- everything can be referred to by its hash and names are just metadata, so its easy to rename stuff and perform other similar magic like caching tests
- Unison has typed documentation which prevents it from going out of sync with the code

## Missing features <a id="missing-features"></a> [↩](#toc)

This wishlist is not comprehensive. We could probably do better (i.e. have more nice things), but we have to stop somewhere, not to mention that all the interactions between all the different features blow up the complexity of the language dramatically.

Other missing features:
- Algebraic Effects

### Typed Holes

Holes are a way of leaving a part of a term unfilled as a kind of local "axiom". They can be later revisited with the help of the language's type inference, filled automatically or serve as names for goals in the proving mode. More ambitious works try to use holes for accomodating ill-typed, ill-formed and incomplete (yet unwritten) programs into the semantics.

Papers:
- [Live Functional Programming with Typed Holes](https://dl.acm.org/doi/pdf/10.1145/3290327)

TODO:
- Typed Holes have something to do with First-Class Patterns. And what if we could make typed holes first-class?

### Quantitative Type Theory

Papers:
- [I Got Plenty o’ Nuttin’](https://personal.cis.strath.ac.uk/conor.mcbride/PlentyO-CR.pdf)
- [Syntax and Semantics of Quantitative Type Theory](https://bentnib.org/quantitative-type-theory.pdf)

### Graded Type Theory

Papers:
- [A Graded Dependent Type System with a Usage-Aware Semantics (extended version)](https://arxiv.org/pdf/2011.04070.pdf)
- [Graded Modal Dependent Type Theory](https://arxiv.org/pdf/2010.13163.pdf)
- [Combining Effects and Coeffects via Grading](https://cs-people.bu.edu/gaboardi/publication/GaboardiEtAlIicfp16.pdf)
- [Quantitative Program Reasoning with Graded Modal Types](https://metatheorem.org/includes/pubs/ICFP19.pdf)
- [Idris 2: Quantitative Type Theory in Practice](https://arxiv.org/pdf/2104.00480.pdf)

Prototypes:
- [Granule](https://github.com/granule-project/granule/blob/main/examples/intro.gr.md) (this link leads to a nice intro with actual code)

Tangential papers (on graded monads):
- [Unifying graded and parameterised monads](https://arxiv.org/pdf/2001.10274.pdf)
- [Towards a Formal Theory of Graded Monads](https://www.researchgate.net/publication/309092270_Towards_a_Formal_Theory_of_Graded_Monads)
- [Relational Algebra by Way of Adjunctions](https://dl.acm.org/doi/pdf/10.1145/3236781) ([slides](http://www.cs.ox.ac.uk/jeremy.gibbons/publications/reladj-dbpl.pdf))