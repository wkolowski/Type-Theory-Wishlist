# Type Theory Wishlist

This repo is a playground in which I'm trying to invent a better type theory/proof assistant/dependently-typed programming language. This README describes the basic syntax and type structure of the language. Each section describes a particular feature of the language by example using concrete syntax, points to relevant papers and discusses its status (like "satndard", "prototype implemented somewhere" or "unsubstantiated speculation"). The details are laid out in subdirectories (linked to by section headers), in files with the `.ttw` extension that contain commented pseudocode which shows each feature in action. At the end we point to some ideas and TODOs for later consideration. 

## Table of Contents <a id="toc"></a>

When reading on GitHub, you can click in the upepr-left corner, near the file name, for an always-up-to-date table of contents.

1. [The Guiding Principle of Syntax](#guiding-principle)
1. [Basic syntax](#basic-syntax)
1. [Types](#types)
1. [Primitive types and arrays](#primitives)
1. [Functions](#functions)
1. [Paths and the rest of Cubical Type Theory](#paths)
1. [Names and Nominal Function Type](#names)
1. [Empty and Unit](#empty-and-unit)
1. [Records (and sums)](#records)
1. [Basic Inductive Types](#basic-inductive-types)
1. [Pattern matching on steroids](#pattern-matching)
    1. [Overlapping and Order-Independent Patterns](#overlapping-patterns)
    1. [Decidable Equality Patterns](#decidable-equality-patterns)
1. [Inductive Families](#inductive-families)
    1. [Standard Inductive Families (TODO)](#standard-inductive-families)
    1. [Indices that Compute (TODO)](#indices-that-compute)
1. [Advanced Inductive Types](#advanced-inductive-types)
    1. [Constructors that Compute](#constructors-that-compute)
    1. [Higher Inductive Types](#HIT)
    1. [Nominal Inductive Types](#nominal-inductive-types)
    1. [Induction-Induction](#induction-induction)
    1. [Induction-Recursion](#induction-recursion)
1. [Basic Coinductive Types](#basic-coinductive-types)
1. ["Positive" Coinductive Types](#positive-coinductive-types)
1. [Coinductive Families](#coinductive-families)
1. [Advanced Coinductive Types](#advanced-coinductive-types)
1. [Refinement types (TODO)](#refinements)
1. [Universes (TODO)](#universes)
1. [Subtyping, coercions and subtype universes (TODO)](#subtyping)
1. [Singleton Types (TODO)](#singletons)
1. [Type-level rewriting (TODO)](#type-level-rewriting)
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

TODO:
- Revisit the comment syntax.
- Invent syntax for documentation comments.
- Documentation is well known for its tendency to go out of sync with the code. So maybe it's time to make it strongly-typed? See [the Unison Language](https://www.unisonweb.org/docs/documentation) for more on typed documentation.

## Types <a id="types"></a> [↩](#toc)

| Name              | Formation        | Introduction     | Elimination      |
| ----------------- | ---------------- | ---------------- | ---------------- |
| Primitive types   | `i8`, `i16`, `i32`, `i64` <br> `u8`, `u16`, `u32`, `u64` <br> `f32`, `f64` <br> `Char` <br> `Text` | literals         | primitive ops    |
| Arrays            | `Array A n`      | literals <br> library functions | `A[i]`     |
| Record types      | `(a : A, ...)`   | `(a => e, ...)`  | `p.x`            |
| Sum types         | not sure         |                  |                  |
| Function type     | `(x : A) -> B x` | `fun x : A => e` | `f a`            |
| Path type         | `x = y`          | `path i => e`    | `p i`            |
| Empty type        | `Empty`          | impossible       | `abort`          |
| Unit type         | `Unit`           | `unit`           | not needed       |
| Name              | `Name A`         | with `∇` and `ν` | pattern matching |
| Nominal function type | `∇ α : A. B α`   | `ν α : A. e`     | `t @ α`          |
| Inductive types   |  see below       | constructors     | pattern matching |
| Coinductive types |  see below       | copattern matching | field selection |
| Strict universes  | `Type h p`       | `Type h p`       | impossible       |
| Non-strict universes | `hType h p`   | `hType h p`      | impossible       |
| Subtype universes | `Sub A`          | implicit (?)     | implicit (?)     |
| Refinement types  | `{x : A \| P x}` | implicit (?)     | implicit (?)     |

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
% Fail
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
- How does it work at the level of formal rules?
- Decide the details of the char type.
- Decide the details of division by zero.
- We may also want to have other char types, like `Ascii` and `UTF-16`.
- Alternatively, `Char` could be made more abstract and the encoding is just its property.
- Maybe disambiguate array literal syntax from syntax sugar for lists?

## Functions <a id="functions"></a> [↩](#toc)

Function types work mostly as usual, except that we want to think that all functions (including dependent ones) take just one argument which is a big (dependent) record. This view is distinct from the usual "every function takes one argument, and then maybe returns another function".

```
f : (x y : A) -> B :=
  fun x y : A => ...
```

Typical (non-recursive) function definition.

```
f (x y : A) : B := ...
```

We can bind arguments together with the name, to the left of the final colon.

```
id (#A : Type) (x : A) : A := x
```

There is a mechanism of implicit arguments. The syntax is inspired by [the F* language](https://www.fstar-lang.org/).

```
comp1 (#A #B #C : Type) (f : A -> B) (g : B -> C) (x : A) : C := g (f x)

comp2 #(A B C : Type) (f : A -> B) (g : B -> C) (x : A) : C := g (f x)
```

If there are many implicit arguments, like in `comp1` above, the syntax gets quite heavy. This is why we can prefix `#` in front of a group of arguments, like in `comp2` above, which makes them all implicit at once.

```
// Function composition with the middle type (`B`) explicit.
comp3 #(A @B C : Type) (f : A -> B) (g : B -> C) (x : A) : C := g (f x)

// An equivalent but longer definition of the above.
comp3' (#A : Type) (B : Type) (#C : Type) (f : A -> B) (g : B -> C) (x : A) : C := g (f x)
```

But then syntax gets heavy when we want to mark as implicit all argument in a group except one. In such cases, we may prefix the argument with `@` (inspired by Coq's and Haskell's syntax for explicit arguments), which overrides the group's implicitness.

```
id (x : A) : A := x

comp (f : A -> B) (g : B -> C) (x : A) : C := g (f x)
```

We can omit writing implicit arguments altogether when they are easily inferable from something else. This piece of syntax is inspired by [Idris 2](https://idris2.readthedocs.io/en/latest/tutorial/typesfuns.html#implicit-arguments). We will call it "super implicit arguments". It is used pretty often in this repo, almost always with `A` and `B` standing in for types.

There are also other kinds of implicitness, like looking up typeclass instances, but these are dealth with by [records](#records).

```
(|>) (x : A) (f : A -> B) : B := f x

(<|) (f : A -> B) (x : A) : B := f x

(>>) (f : A -> B) (g : B -> C) (x : A) : C := g (f x)

(<<) (g : B -> C) (f : A -> B) (x : A) : C := g (f x)
```

Names of functions are allowed to consist entirely of symbols, although this style is discouraged except for the most common functions, like the above operators borrowed from F#: pipe forward `|>`, pipe backward `<|`, forward function composition `>>` and backward function composition `<<`.

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

There are two syntaxes for operator sections. The first one (`(* 3)` above) is borrowed from Haskell and works only for already-defined functions whose names are symbols. The second one (`(_ `mod` 2 =? 0)` above) works for any expression that represents a single-argument function, with the underscore `_` used to mark the argument. We can turn any function into an infix operator by enclosing the function's name in backticks, like for `mod` above.

Together with the pipe operators and function composition operators, this makes data processing easy and readable.

```
self-comp (h : Nat -> Nat) : Nat -> Nat :=
  comp {A => Nat, B => Nat, C => Nat} {g => h} {f => h}
```

Functions can be applied not only positionally, but also by naming the argument. With such application, the order of the arguments doesn't matter anymore. This is also useful when we need to explicitly provide an implicit argument.

```
self-comp' (h : Nat -> Nat) : Nat -> Nat :=
  comp {C, A, B => Nat; f, g => h}
```

To reiterate: the order of arguments doesn't matter. As a bonus, we can set many arguments to the same value very easily - this should be very useful easpecially for type arguments.

```
complex-application
  (f : (x1 : A) (x2 : B) (x3 : C) (x4 : D) (x5 : E -> E') (x6 : F) (x7 : G -> G') -> X) : X :=
  f $
    arg1
    x2 => arg2
    x4 => arg4
    arg3
    fun x => ...
    arg6
    x7 => fun y => ...
```

Last but not least, there is special syntax for applying functions which have a lot of complex arguments. To apply a function `f` in this way, we write `f $` and then list the arguments below on separate lines. We can supply the arguments positionally in order and also by name, in which case they can appear out of order. This syntax is inspired by Haskell's `$` operator, and may also be used to avoid parenthesis hell when a function takes a lot of other functions as arguments.

**Status: mostly standard, with `@` for explicit arguments and `$` for complex application being new, but very easy to implement.**

TODO:
- Figure out the precise workings of "all functions take just one argument which is a big record".
- Describe default and optional arguments and how they relate to record types.

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
& x => p.x + n
& _ => p
```

Copatterns also allow the modify syntax.

```
translateX (n : Nat) (p : (x y z : Nat)) : (x y z : Nat)
& x $=> (+ n)
& _ => p
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

Modules can use prototypes too, but this time we should put them at the top of the module.

```
translateX (n : Nat) (p : (x y z : Nat)) : (x y z : Nat) :=
module
  inherit p

  x : Nat => p.x + n
end
```

The modify syntax also works with modules - no surprise there.

```
translateX (n : Nat) (p : (x y z : Nat)) : (x y z : Nat) :=
module
  inherit p

  x : Nat $=> (+ n)
end
```

### Record types with manifest fields.

Our record types can have some fields set in advance, like the following type of points that have `x`, `y` and `z` coordinates, but the `z` coordinate is set to zero.

```
p : (x y : Nat, z : Nat := 0) := (x => 1, y => 2)
```

We can access `z` even though we didn't explicitly set it.

```
p-z : Nat := p.z
```

In fact, after setting a field, the type of the result reflects this.

```
translateX (n : Nat) (p : (x y z : Nat)) : (x : Nat := p.x + n, y z : Nat) :=
  (x => p.x + n & p)
```

Because we already wrote it at the type level, we may omit it at the term level.

```
translateX (n : Nat) (p : (x y z : Nat)) : (x : Nat := p.x + n, y z : Nat) :=
  (& p)
```

### Operations on record types.

We can combine multiple record types with the join operator.

```
example-join-1 : (outl : A) & (outr : B) = (outl : A, outr : B) := refl
```

We can also combine record types dependently.

```
example-join-2: (outl : A) & (outr : B outl) = (outl : A, outr : B outl) := refl
```

The join operation preserves implicitness of arguments.

```
example-join-3 : (#outl : A) & (outr : B outl) = (#outl : A, outr : B outl) := refl
```

#### Renaming.

Given a record type, we can rename its fields to get another record type.

```
example-rename-1 :
  (x y z : Nat) renaming (x to a) = (a y z : Nat) := refl
```

Renaming also works on manifest fields.

```
example-rename-2 :
  (x y : Nat, z : Nat := 0) renaming (z to w) = (x y : Nat, w : Nat := 0) := refl
```

Setting a field.

```
example-set-1 :
  (x y z : Nat) setting (z := 0) = (x y : Nat, z : Nat := 0) := refl
```

Unsetting a field.

```
example-unset-1 :
  (x y : Nat, z : Nat := 0) unsetting z = (x y z : Nat)
```

We can remove a field to get a new record type.

```
example-removing :
  (x y z : Nat) removing z = (x y : Nat)
    := refl
```

### General record type prototyping.

We can combine joins, renaming, setting, unsetting and removing into a single operation. This way we can create a new record type from a given prototype record type.

```
example-prototyping :
  (x y : Nat, z : Nat := 0, n : Nat) with (x to a := 5, y to b, unset z, remove n)
    =
  (a : Nat := 5, b z : Nat)
    := refl
```

### Record subtyping.

We have a subtyping relation between records. This does not mean that we have subtyping in our language (yet; see the directory Subtypes/), this is just for illustration purposes.

Bigger record types are subtypes of smaller record types.

```
(x y z : Nat) <= (x y : Nat)`
```

But record types with manifest fields are subtypes of record types without fields set.

```
(x y : Nat, z : Nat := 0) <= (x y z : Nat)
```

Record types made with a join are subtypes of their arguments.

```
r1 & r2 <= r1
r1 & r2 <= r2
```

Of course all record types are subtypes of the empty record type.

```
R <= ()
```

// TODO: how this works with dependent records?

### The Solution of our Problems

Let's solve the problems we have.

#### Problem 1: globally unique field names.

Record field names need not be globally unique. In case they clash, we can disambiguate manually.

```
Point2D : Type := (x y : Nat)
Point3D : Type := (x y z : Nat)

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

#### Problem 2: no definitional uniqueness principle for records.

Records do have a definitional uniqueness principle!

```
definitional-uniqueness-for-records
  (r : (a : A, b : B a)) : r = (a => r.a, b => r.b) := refl
```

There's also a uniqueness principle for prototypes.

```
uniqueness-principle-for-prototypes
  (r : (a : A, b : B a)) : r = (& r) := refl
```

#### Problem 3: hard to prove record equality.

This one is probably more a matter of cubical stuff than of records themselves.

TODO!

#### Problem 4: hard to reuse record types.

First, we can define record types in a copattern(-like) syntax.

```
Refl : RType
  A : Type
  R : A -> A -> Prop
  reflexive : (x : A) -> R x x

Sym : RType
  A : Type
  R : A -> A -> Prop
  symmetric : (x y : A) -> R x y -> R y x

Trans : RType
  A : Type
  R : A -> A -> Prop
  transitive : (x y z : A) -> R x y -> R y z -> R x z
```

Record types can be joined together. By "join" we mean a kind of non-disjoint union or pushout - fields which have the same names are collapsed into one, and those that have different names remain separate.

```
Equiv' : RType := Refl & Sym & Trans
```

The above join is equal to the manually encoded record type that represents equivalence relations.

```
Equiv' : RType
  A : Type
  R : A -> A -> Prop
  reflexive : (x : A) -> R x x
  symmetric : (x y : A) -> R x y -> R y x
  transitive : (x y z : A) -> R x y -> R y z -> R x z

Equiv-is-Refl-Sym-Trans :
  Equiv = Equiv' := refl
```

#### Problems 5: telescopization stemming from lack of inheritance.

We can also use record types as prototypes to construct other record types.

```
Magma : RType
  A : Type
  op : A -> A -> A
```

Here a semigroup is a magma extended with associativity. `Pointed` represents a pointed type, i.e. a type together with its element.

```
Semigroup : RType :=
  Magma &
  assoc : (x y z : A) -> op (op x y) z = op x (op y z)

Pointed : RType
  A : Type
  point : A
```

We can also rename fields during the join.

```
Monoid : RType :=
  Semigroup &
  (Pointed renaming point to id) &
  idl : (x : A) -> op id x = x
  idr : (x : A) -> op x id = x

Monoid' : RType
  A : Type
  op : A -> A -> A
  assoc : (x y z : A) -> op (op x y) z = op x (op y z)
  id : A
  idl : (x : A) -> op id x = x
  idr : (x : A) -> op x id = x

Monoids-same : Monoid = Monoid' := refl
```

#### Problem 6: hard to unbundle record types into typeclasses.

We can easily obtain a typeclass by setting a field in the `Monoid` type. For now, we ignore the matter of what a typeclass is.

```
MonoidClass (A : Type) : RType :=
  Monoid setting A to A
```

This is the result of the above definition written more explicitly.

```
MonoidClass' (A : Type) : RType
  op : A -> A -> A
  assoc : (x y z : A) -> op (op x y) z = op x (op y z)
  id : A
  idl : (x : A) -> op id x = x
  idr : (x : A) -> op x id = x

MonoidClass-MonoidClass' : MonoidClass = MonoidClass' := refl
```

We can also reverse these operations and bundle MonoidClass' to get a record type.

```
Monoid' : RType :=
  A : Type
  & MonoidClass' A

Monoid-Monoid' : Monoid = Monoid' := refl
```

#### Problem 7: currying/uncurrying of functions and the relationship between records and function arguments.

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

We can convert between these two representations (arguments collected into a record and freestanding arguments) using the currying/uncurrying operator &.

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

Papers on dependent records in type theory:
- [Dependent Record Types Revisited](http://www.cs.rhul.ac.uk/home/zhaohui/DRT11.pdf)
- [Typed Operational Semantics for Dependent Record Types](http://www.cs.rhul.ac.uk/home/zhaohui/TYPES09final11-01-01.pdf)
- [Extension of Martin-Löf's Type Theory with Record Types and Subtyping](https://www.researchgate.net/publication/2683061_Extension_of_Martin-Lof's_Type_Theory_with_Record_Types_and_Subtyping)
- [Ur: Statically-Typed Metaprogramming with Type-Level Record Computation](http://adam.chlipala.net/papers/UrPLDI10/UrPLDI10.pdf)
- [Abstracting Extensible Data Types: Or, Rows by Any Other Name](https://www.pure.ed.ac.uk/ws/portalfiles/portal/87175778/Abstracting_extensible_data_types_MORRIS_DoA_tbc_VoR_CC_BY.pdf)

Not papers:
- [a wild and more ambitious idea of what records should be](Records/TurboRecords.ttw)

**Status: mostly wild speculations. The papers promise much, but no good implementations/prototypes, so probably there's something wrong with them. Sums probably won't happen.**

TODO:
- Finish thinking about records.
- How to turn typing contexts into record types? This would free us from some duplication at the meta level. But beware! This is not the same idea as "first-class typing contexts" and certainly not the same as "first-class evaluation contexts".
- Rethink modify syntax for modules.
- Rethink whether the prototype should really go at the end of the record definition.

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

In the definition of the type of `List`s below, this manifests in that we write `tl : List` for the tail of the list instead of `tl : List A` as we would if `A` were an index. Also note that we allow constructor names to by symbols, including infix symbols, just like in Agda.

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

**Status: inductive types and pattern matching are standard, with Agda probably being the closest implementation to what has been described so far.**

TODO:
- Make sure that `@` used for as-patterns doesn't clash with `@` used for explicit arguments and `@` used for name concretion.
- Describe the fact that constructor names need not be unique and that every inductive types has its own namespace. The same for coinductives.

## Pattern matching on steroids <a id="pattern-matching"></a> [↩](#toc)

Besides the usual pattern matching, we also allow some extensions which significantly increase it's power:
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
head : (#n : Nat) (v : Vec (s n)) -> A
| .n', Cons h n' t => h
```

We call these _forced patterns_, contrary to [Agda](https://agda.readthedocs.io/en/v2.5.2/language/function-definitions.html#special-patterns) which calls them _inaccessible patterns_.

Papers:
- [Pattern Matching Without K](https://jesper.sikanda.be/files/pattern-matching-without-K.pdf)
- [A Syntax for Mutual Inductive Families](https://drops.dagstuhl.de/opus/volltexte/2020/12345/pdf/LIPIcs-FSCD-2020-23.pdf)

**Status: inductive families are standard in proof assistants and dependently-typed languages. Dependent pattern matching is semi-standard, as some languages (notably Coq) have problems with supporting it properly so it's hard to use, while some others (Idris 2 and formerly Agda) have implementations of it that entail Uniqueness of Identity Proofs, which is incompatible with Univalence. The closest implementation of what's described here is probably Agda (with the flag `--without-K`).**

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
- [Vectors are records, too](https://jesper.sikanda.be/files/vectors-are-records-too.pdf)
- [Slides for the above](https://jesper.sikanda.be/files/TYPES2018-presentation.pdf)
- [A simpler encoding of indexed types](https://dl.acm.org/doi/10.1145/3471875.3472991)

**Status: very wild speculations.**

TODO:
- Think about this more.
- Figure out what nonstandard techniques are allowed by having [manifest fields in constructors](Induction/IndicesThatCompute/IndicesThatCompute.ttw).

## [Advanced Inductive Types](Induction) <a id="advanced-inductive-types"></a> [↩](#toc)

Inductive families are just the tip of the iceberg, as our inductive types are supposed to be REALLY powerful. We take the usual inductive families as baseline and add:
- [Constructors that Compute](#constructors-that-compute)
- [Higher Inductive Types](#higher-inductive-types)
- [Nominal Inductive Types](#nominal-inductive-types)
- [Induction-Induction](#induction-induction)
- [Induction-Recursion](#induction-recursion)

We have listed the various enhancements in order from most to least wild. We take the former ones for granted when describing the latter, so as to show their synergy.

### [Constructors that Compute](Induction/ConstructorsThatCompute) <a id="constructors-that-compute"></a> [↩](#toc)

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

See [this file](Induction/ConstructorsThatCompute/Z.ttw) for a more thorough explanation and exploration of the type of integers defined using Constructors that Compute.

Papers:
- None, this idea is brand new invention of mine.

**Status: highly experimental. It looks like if we put reasonable constraints on the kinds of computation rules associated with constructors, there isn't any abvious contradiction, nontermination or anything like that. However, there are no prototypes and no papers, except that some Constructors that Compute can be simulated using [Self Types](https://github.com/uwu-tech/Kind/blob/master/blog/1-beyond-inductive-datatypes.md).**

TODO:
- Come up with more examples of useful Constructors that Compute.

### [Higher Inductive Types](Induction/HIT) <a id="HIT"></a> [↩](#toc)

Higher Inductive Types are inductive types which can be defined using not only point ("ordinary") constructors, but also path constructors which put additional paths into the type. This has two serious uses: the more practical one is for making all kinds of quotients and quotient-like types (and a lot of these can't be made using Constructors that Compute, because there is no canonical form of some collection of terms) and the more theoretical one is synthetic homotopy theory.

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
- [LARGE AND INFINITARY QUOTIENT INDUCTIVE-INDUCTIVE TYPES](https://arxiv.org/abs/2006.11736)
- [Quotient inductive-inductive types](https://arxiv.org/abs/1612.02346)
- [Codes for Quotient Inductive Inductive Types](https://akaposi.github.io/qiit.pdf)
- [Constructing quotient inductive-inductive types](https://akaposi.github.io/finitaryqiit.pdf)
- [Quotient inductive-inductive definitions](http://eprints.nottingham.ac.uk/42317/1/thesis.pdf)
- [A model of type theory with quotient inductive-inductive types](http://real.mtak.hu/112971/1/1.pdf)
- [Higher Inductive Types, Inductive Families, and Inductive-Inductive Types](http://von-raumer.de/academic/phd_vonraumer.pdf)
- [A Syntax for Higher Inductive-Inductive Types](https://drops.dagstuhl.de/opus/volltexte/2018/9190/pdf/LIPIcs-FSCD-2018-20.pdf)
- [SIGNATURES AND INDUCTION PRINCIPLES FOR HIGHER INDUCTIVE-INDUCTIVE TYPES](https://lmcs.episciences.org/6100/pdf)
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

We can combine induction-recursion with Constructors that Compute to get a more interesting kind of universe - one in which the various type isomorphisms hold by definition. For the boring isomorphisms like `Empty + A = A` this is not very useful (as it's helpful only rarely), but it's extremely useful for the equality type - thanks to Constructors that Compute we can have `(f = g) = (x : A) -> f x = g x` and `((x1, y1) = (x2, y2)) = (x1 = x2) * (y1 = y2)` and so on.

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
- [Higher inductive-recursive univalence and type-directed definitions](https://homotopytypetheory.org/2014/06/08/hiru-tdd/) - see for a definition of universe with type-directed equality like the one presented above, but using higher-inductive types instead of constructor that compute
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

Papers:
- [Copatterns Programming Infinite Structures by Observations](https://www.researchgate.net/profile/Anton-Setzer/publication/262366004_Copatterns_Programming_Infinite_Structures_by_Observations/links/587fe0f208ae9275d4ee3ae2/Copatterns-Programming-Infinite-Structures-by-Observations.pdf)
- [Unnesting of Copatterns](http://www2.tcs.ifi.lmu.de/~abel/rtatlca14.pdf)
- [Wellfounded Recursion with Copatterns and Sized Types](http://www2.tcs.ifi.lmu.de/~abel/jfp15.pdf)
- [Elaborating dependent (co)pattern matching](https://jesper.sikanda.be/files/elaborating-dependent-copattern-matching.pdf)
- [Copattern matching and first-class observations in OCaml, with a macro](https://hal.inria.fr/hal-01653261/document)

Not papers:
- [Pattern and Copattern matching](http://www1.maths.leeds.ac.uk/pure/logic/images/slidesLeedsLogicSeminarMay2015.pdf)

**Status: negative inductive types are imeplemented in Agda and Coq. Additionally, copattern matching is implemented in Agda. The Agda implementation of copatterns is based on one of the papers, which means things look pretty good.**

TODO:
- Maybe if we start with patterns, then the definition should still be interpreted as legal corecursive definition?
- Overlapping and Order-Independent Copatterns.
- Another possibility for handling coinductives is for them to be just (co)recursive records, but this depends on how cool and foreign records will be.

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

**Status: somewhat experimental. There are no papers nor a prototype implementation. However, it looks pretty reasonable and I have some Coq code [here](Coinduction/Code/Vec.v) that shows an example manual desugaring.**

TODO:
- Check the details.

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

We'll explore the above in the following subsections. To avoid giving you a headache, we'll start with the status of it all.

Papers:
- There are quite a few papers on mixing coinduction with induction, but most of them are written in the old deprecated Agda-style coinduction, so they aren't that much useful. We are going to list them, nevertheless (this time in chronological order (oldest first), not in order of relevance):
- [Continuous Functions on Final Coalgebras](https://core.ac.uk/download/pdf/82531251.pdf)
- [REPRESENTATIONS OF STREAM PROCESSORS USING NESTED FIXED POINTS](https://arxiv.org/pdf/0905.4813.pdf)
- [Mixing Induction and Coinduction](https://www.cse.chalmers.se/~nad/publications/danielsson-altenkirch-mixing.pdf)
- [Subtyping, Declaratively: An Exercise in Mixed Induction and Coinduction](https://www.cse.chalmers.se/~nad/publications/danielsson-altenkirch-subtyping.pdf)
- [Mixed Inductive-Coinductive Reasoning](https://liacs.leidenuniv.nl/~basoldh/thesis/Thesis.pdf) (PhD thesis from 2016, 340 pages, probably the best place to look for more papers on the topic, also probably contains a good introduction and overview)
- [THE SIZE-CHANGE PRINCIPLE FOR MIXED INDUCTIVE AND COINDUCTIVE TYPES](https://arxiv.org/pdf/1901.07820.pdf)
- [Integrating Induction and Coinduction via Closure Operators and Proof Cycles](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC7324239/)

**Status: mostly speculation, but based on the solid "positive" coinductive syntax sugar and solid principles. It looks mostly doable.**

TODO:
- Currently using pattern matching means that the function is recursive, so the second definition of `toStream` is not legal. Maybe some annotation for whether a function is recursive or corecursive?
- Does `let` and copattern matching play out together as nicely as in the last example?
- Reconsider the `mutual` keyword for mutual coinductive-inductive definitions.

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

The second attempt results in a much more compact definition. `toStream` is still corecursive, but we use pattern matching at the top level to make the definition shorter. In the `Put` case, we unpack the head of the stream from the argument and compute the tail corecursively, just as in the first definition. In the `Get` case, we use `toStream'`, which computes the result stream recursively from `g : GetSP A B` and `s : Stream A`. In the `Put` case, it behaves the same as `toStream`, whereas in the `Get` case it recursively feeds the input stream `s` into `g`. As we can see, we managed to cut down the redundancy.

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

### Untangleable coinduction-induction?

TODO

### Untangleable coinduction-coinduction?

TODO

## Refinement types <a id="refinements"></a> [↩](#toc)

The idea is to have, for every type `A`, the type `{x : A | P}` where `P` is some decidable strict proposition that the typechecker (or some external SMT solver, but that's meh...) can reason about. The pioneer in this space is [the F* language](https://www.fstar-lang.org/).

F* also has some additional nice features related to refinement types that make life a lot easier:
- Discriminators that check which constructor was used to make the given term, e.g.:
  - `Nil? : list 'a -> bool`
  - `Cons? : list 'a -> bool`
- Projections which project constructor arguments out of a term (given that the term was really made using that constructor):
  - `Cons?.hd : l : list 'a{Cons? l} -> 'a`
  - `Cons?.tl : l : list 'a{Cons? l} -> list 'a`
- Note that the above are written in F* syntax and require refinement types to get anywhere.

Papers:
- TODO

**Status: implemented in F\*, works pretty well there.**

TODO:
- Hunt for papers.
- Figure out relation between refinement types and dependent records with fields in `Prop`.
- Figure out relationship between refinement types and inductive/coinductive types.

## [Universes](Universes/Universes.md) <a id="universes"></a> [↩](#toc)

We want to have a multidimensional hierarchy of universes stratified both by the usual predicative level and by homotopy level, similar to the [Arend language](https://arend-lang.github.io/about/arend-features#universe-levels). The predicative levels are basically naturals, whereas the homotopy levels are natural numbers extended with infinity (for untruncated types). In fact, there will be (at least) two type hierarchies: the strict one and the non-strict one.

In the strict hierarchy, `Type (h = 0)` (abbreviated `Contr`) is the universe of contractible types (whose only member is itself), `Type (h = 1)` (abbreviated `Prop`) is the universe of strict (i.e. definitionally irrelevant) propositions (like Coq's [Prop](https://coq.inria.fr/refman/addendum/sprop.html) or Agda's [Prop](https://agda.readthedocs.io/en/v2.6.0/language/prop.html)), `Type (h = 2)` (abbreviated `Set`) is the universe of strict sets (types for which the type of paths is a strict proposition) and so on, up to `Type (h = oo)`, the universe of strict untruncated types.

The non-strict hierarchy (written `hType`) is similar. Knowing that a type has a homotopy level `h` should bring benefits which are similar but weaker than these for the strict universes.

### Idea

We want our universes to keep track of types' homotopy levels. This could:
- Give us more computational equalities by explicitly marking types as "strict propositions" (no computational content, i.e. all terms computationally equal), "strict sets" (paths are strict propositions) and so on. We call universes that are capable of this **strict universes**.
- Free us from boilerplate stemming from having to pass around proofs of being a proposition (`isProp`), a set (`isSet`) and so on and having to use them where appropriate. We call universes that are capable of this **non-strict** universes.

### Syntax

We denote the strict universes by `Type h p`. We can be more explicit by writing `Type (h = h', p = p')`. We allow "typical ambiguity", i.e. when the level is not written, it will be inferred and solved by the universe checker. We can be more explicit and ambiguous at once, for example writing `Type (h = h')` - the homotopy level is explicit, but the predicative level will be inferred. We abbreviate `Type (h = 0)` with `Contr`, `Type (h = 1)` with `Prop`, `Type (h = 2)` with `Set` and `Type (h = 3)` with `Grpd`.

Non-strict universes follow the same conventions, except that they are called `hType` and the abbreviations for the various h-levels are `hContr`, `hProp`, `hSet` and `hGrpd`, respectively.

We use Russell style universes because they are easier to read and write.

### Levels

The predicative levels are natural numbers and the homotopy levels are natural numbers extended with infinity (written `oo`). Whether levels stay at the metatheoretical level (nice pun, no?) or become first-class (by turning into the types `Nat` for p-levels and `hlvl` for h-levels) remains to be seen. In case we want it, we have `plvl : Set` (with `plvl` definitionally equal to `Nat`), `hlvl : Set` and we also need a universe `TYPE` which contains all universes `Type h p` and `hType h p` for all `h : hlvl` and all `p : plvl`.

Operations on levels include `pred` and `max`, which definitionally satisfy (or are defined as, in case levels are first-class) the following equations:

```
pred : hlvl -> hlvl
| 0     => 0
| l + 1 => l
| oo    => oo
```

```
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
// All proof of a strict proposition are computationally equal.
isProp-from-Prop (#A : Prop) (x y : A) : x = y := refl
```

We then extend the hierarchy upwards. This is done with the formation rule for equality type/`Path` type, which says that if `A : Type h p` and `x y : A`, then `x = y : Type (pred h) p` (and similarly for `hType`; from now we will omit `hType` and concern ourselves only with `Type`).

But beware: for this to work, `=` can't be an inductive family (because if it were, it would get placed in the wrong universe). Instead, it must be built-in. So we either need to have a separate inductive-like equality or a `Path` type with the appropriate formation rules.

How this works in practice:

```
// `A : Set`, so `x = y : Prop` and so trivially `p = q`.
isSet-from-Set (#A : Set) #(x y : A) (p q : x = y) : p = q := refl
```

```
// Analogously for strict groupoids.
isGrpd-from-Grpd (#A : Grpd) #(x y : A) #(p q : x = y) (r s : p = q)
  : r = s := refl
```

At last, we need to return back to the zeroth level of the hierarchy and set up the universe `Contr` (unless we consider this universe silly and want to drop it). The formation rule is `Contr : Contr` and it becomes fully functional when we allow cumulativity between `Contr` and `Prop`, i.e. `A : Contr` implies `A : Prop`.

### Basic mechanics of non-strict universes

The typing rules for non-strict universes are analogous to those for strict universes, but the benefits are somewhat different - they amount to not needing to handle some cases when defining function by patterns matching whose domain is known to be of some h-level.

This is because to define a function into an `n`-type, we only need to handle constructors of dimension less than or equal to `n - 1`. For example, when the codomain is a set, we only need to consider point constructors (obviously) and path constructors (so that we don't disconnect points which were connected), but not 2-dimensional path constructors (as all 2-paths in a set are contractible).

These benefits multiply enormously when matching two or more values. For example, proving a property of two elements of a [free group defined like this](../Induction/HIT/FG.ttw) requires only 9 cases instead of 49.

### Formation rules

| Name             | Rule             |
| ---------------- | ---------------- |
| Strict universes | `Type h p : Type (h + 1) (p + 1)` |
| Non-strict universes | `hType h p : hType (h + 1) (p + 1)` |
| Path type     | if `A : Type h p` <br> and `x y : A` <br> then `x = y : Type (pred h) p` |
| Function type | if `A : Type h1 p1` <br> and `B x : Type h2 p2` (for all `x : A`) <br> then `(x : A) -> B x : Type h2 (max p1 p2)`  |
| Empty type    | `Empty : Prop`  |
| Unit type     | `Unit : Contr`  |
| Record types  | if `A_i : Type h_i p_i` <br> then `(a_i : A_i) : Type (max h_i) (max p_i)` |
| Name type     | if `A : Type h p` <br> then `Name A : Type 2 p` |
| Nabla type    | if `B α : Type h p` <br> then `∇ α : A. B α : Type h p` |
| Subtypes      | if `A : Type h p` <br> then `Sub A : Type (max 2 (h + 1)) p` |
| Refinements   | if `A : Type h p` <br> and `P : A -> Prop` <br> then `{x : A \| P x} : Type h p` |
| Inductives    | see below           |
| Coinductives  | see below           |

Function types inherit their h-levels from their codomains. `Empty` is a strict proposition and `Unit` is contractible. Records are placed in the `max`imal universe of their (h and p)-levels. Names have decidable equality, so it only makes sense for `Name A` to be a strict set. Nabla types are similar to functions in that they inherit their h-level from the codomain. Refinement types stay at the same level as they carry just a proof of a strict proposition.

A more interesting case is that of subuniverses. For `Empty` the type `Sub Empty` is contractible, but for non-empty types it always has at least two elements (`Empty` and the type itself), so it's always at least a set. This is why the first argument of `max` is `2` in the typing rule.

Moreover, `Sub Bool` has `Bool` as an element, and there are precisely two paths `Bool = Bool`, so `Sub Bool` is not a set, but a groupoid. This suggests that `Sub` behaves similarly to universes, i.e. raises the h-level by one. This is why the second argument of `max` in the typing rule is `h + 1`.

Last but not least, inductive types. It is easy to determine the h-level of constructor arguments (since they are records; note that we need to ignore the inductive arguments), but for the whole type some heuristics are needed. If there are at least two constructors, the h-level is at least 2 (i.e. the type is a strict set). It may well be that the constructor's arguments are disjoint (like `P` and `~ P`), but in general this is undecidable, so we don't care. If constructors are disjoint (i.e. we're not dealing with a higher inductive type) then the h-level will be maximum of 2 and the constructors' h-levels. If we're dealing with a HIT, things become infinitely more complicated and we may just as well say that the h-level of the whole type is `oo`.

Coinductive types can be handled similarly to records, but we need to ignore the h-level of coinductive fields when taking the `max`imum.

### Truncation

If the h-level of a type cannot be determined, we can **truncate** the type, i.e. force it into the desired level. We can also truncate the type when the h-level is inferred to be greater than what we want.

This feature allows us to define the operation known under many names: propositional truncation/propositional reflection/Squash type/etc. Importantly, we can do this even if we don't have [Higher Inductive Types](../Induction/HIT).

```
// Propositional truncation.
%Truncated
data Squash (A : Type) : hProp
| sq (x : A)
```

```
// Strict truncation.
%Truncated
data ||_|| (A : Type) : Prop
| |_| (x : A)
```

```
// Also pretty useful one: strict set truncation.
%Truncated
data SetSquash (A : Type) : Set
| in (x : A)
```

The price we must pay for non-strict truncation is that we can eliminate truncated types `A : Type h p` only when constructing elements of types `B : Type h' p'` with `h' <= h`, i.e. of the same or lower h-level.

### Restrictions on elimination of strict propositions

In Coq and Agda there's a restriction on elimination of strict propositions so as to avoid "spilling" the strictness into the outside world, which could result in nontermination, undecidability of type checking and falling into extensional type theory.

This restrction says that inductive strict propositions can be eliminated into ordinary `Type`s if they satisfy some simple critera, which in practice amount to saying that all strict propositions which can be eliminated are built from `Empty`, `Unit` and recursive functions which return either `Empty` or `Unit`. For us, this means that `Empty` and `Unit` can be eliminated into anything at all and that other strict propositions can be eliminated only into other strict propositions.

### Cumulativity

We cannot have cumulativity between strict propositions and larger universes in order to obey the restrictions on elimination. For now this means there's cumulativity between `Contr` and `Prop`, then a GIANT WALL, and then cumulativity starts again from strict sets upwards. So we have `Type 0 p <= Type h p'` for `h = 0` or `h = 1` and `p <= p'`, then a GIANT WALL, and then `Type (2 + h) p <= Type (2 + h') p'` for `h <= h'` and `p <= p'`. Similar rules hold for `hType`.

Additionally we have `Type (2 + h) p <= hType (2 + h) p`, i.e. we may go from a strict universe to a non-strict one if we are at or above the set level, but not the other way around...

### Restriction on elimination of other strict inductive types

What are the restrictions on elimination of strict inductive types at or above the strict set level?

At higher h-levels the criterion for strict propositions generalizes to the criterion that `Type h p` can be eliminated only into `Type h' p'` where `h' <= h`. For example, we can eliminate strict sets into strict sets and strict propositions (and `SContr`), but not into strict grupoids or non-strict types.

But is this really the case? This would mean that we can't define a type family whose domain are the strict natural numbers. Yuck!

```
data SNat : Set
| z
| s (pred : SNat)

// Why would this be evil?
even : SNat -> Type
| z       => Unit
| s z     => Empty
| s (s n) => even n

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

One-not-even : Even (s z) -> Empty :=
let
  P : SNat -> hType
  | 
in
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
- Maybe merge strict and non-strict universes these into one, i.e. `Type s h p`, with `s` being the strict (homotopy) level, `h` the (non-strict) homotopy level and `p` the predicative level? Of course we will then have `h <= s`.

## Subtyping, coercions and subtype universes <a id="subtyping"></a> [↩](#toc)

We want to have subtyping in our type theory, but we want to avoid all the pitfalls associated with subtyping. For this reason, our subtyping judgement shall be proof-relevant, i.e. it should explicitly specify the coercion used to pass from the subtype to the supertype. These coercions should be unique, i.e. there can't be two coercions from `A` to `B`. It should also be possible to declare custom coercions, as long as they don't break uniqueness.

We summarize the rules that govern subtyping in the table below.


| Name              | Rule             | Coercion         |
| ----------------- | ---------------- | ---------------- |
| Strict Universes  | if `i <= j` <br> and `h <= h'` <br> then `Type h i <= Type h' j` | lift |
| Non-strict Universes | if `i <= j` <br> and `h <= h'` <br> then `hType h i <= hType h' j` | lift |
| Primitive signed integers | `i8 <= i16 <= i32 <= i64` | built-in: copy the bits and pad the result with zeros |
| Primitive unsigned integers | `u8 <= u16 <= u32 <= u64` | built-in: copy the bits and pad the result with zeros |
| Primitive floats | `f32 <= f64` | built-in |
| Coercions between signed and unsigned integers | `u8 <= i16` <br> `u16 <= i32` <br> `u32 <= i64` | built-in |
| Char              | `Char <= Text` | make single character text |
| Arrays            | if `c : A <= A'` <br> and `n' <= n` <br> then `Array A n <= Array A' n'` | `map c` and clip the result to the correct length |
| Width-subtyping for record types | `(a : A, r) <= r` | TODO |
| Depth-subtyping for record types | if `c : A <= A'` <br> then `(a : A, r) <= (a : A', r)` | `fun x => (a => c x.a, r => x.r)` |
| Advanced subtyping for records | [complicated](Records/TurboRecords.ttw) | TODO |
| Sums              | `inl : A <= A + B` <br> `inr : B <= A + B` | TODO: uniqueness problems |
| Function type     | if `f : A <= A'` <br> and `g : B <= B'` <br> then `A' -> B <= A -> B'` | `fun h => f >> h >> g` |
| Paths             | if `c : A <= B` <br> then `x ={A} y <= c x ={B} c y` | `fun p => path i => c (p i)` |
| Name              | no subtyping | none |
| Nominal function type | if `c : A <= B` <br> then `∇ α : N. A <= ∇ α : N. B` | `fun x => ν α. c (x @ α)` |
| Inductives        | not sure |
| Coinductives      | not sure |
| `Empty`           | `Empty <= A`     | `abort` |
| `Unit`            | `A <= Unit`      | `fun _ => unit` |
| `Bool`            | `Bool <= Prop`   | `fun b : Bool => b = tt` <br> `fun b : Bool => if b then Unit else Empty` |
| Width-subtyping for refinement types | `{x : A \| P} <= A` | identity |
| Depth-subtyping for refinement types | if `P -> Q` <br> then `{x : A \| P} <= {x : A \| Q}` | identity |
| Subtype universes | if `c : A <= B` <br> then `Sub A <= Sub B` | built-in <br> `c` magically works on subtypes |

Comments:

Our universes are cumulative, i.e. we can lift types from a lower universe to a higher one. They are also cumulative with respect to the homotopy level.

Primitive types have very predictable subtyping - we only allow coercions that don't lose informatiomn, i.e. they are injective.

We allow subtyping for arrays, both through the element type and through length, i.e. longer array types are subtypes of shorter array types.

The matter for records is complicated. The basic principles from other languages are present, i.e. we have width subtyping (bigger record types are subtypes of smaller record types) and depth-subtyping (record types with fields that are subtypes are subtypes of record types with fields that are supertypes). For advanced records that behave like functions, however, it is less clear what the subtyping rules should be like.

Subtyping for functions is standard: contravariant in the domain and covariant in the codomain. This transfers to function-like types, i.e. path types and nominal function types, which are covariant in their codomains, but invariant in their domains (as the interval/name types don't have subtypes).

There's a question of what the correct rules for `Name` and `∇` are. For now `Name` is invariant, but nothing prevents it from being covariant: if `c : A <= B` then `Name A <= Name B` with coercion `map c` for some `map : (A -> B) -> Name A -> Name B`. If `Name` was covariant, then I think (but I'm not sure) that `∇` could be contravariant in its domain, just like the function type.

It's not clear what the rules should be for inductive and coinductive types. However, we have some subtyping for `Empty`, `Unit` and `Bool`. First, `Empty` is a subtype of any type because given `e : Empty` we can just `abort` it. Second, any type is a subtype of `Unit`, because we can just erase it and return `unit`. Third, `Bool` is a subtype of `Prop` so that we can easily go from the world of decidable propositions to the world of all propositions.

For refinement types, we allow making the refinement less precise (depth subtyping) or dropping it altogether (depth subtyping).

Finally, we shall reify the subtyping judgement into a type. The basic idea is that for every type `A` there is a type `Sub A` which represents the universe of subtypes of `A`. The only serious use for this feature presented in the relevant paper is simulating bounded polymorphism and extensible records.

```
translateX (n : Nat) (r : Sub (x : Nat)) : R :=
  (x $=> (+ n) & r)
```

Here we translate the `x`-coordinate by `n` in any record that has a field named `x`, while making sure to return a record of the same type without truncating it.

Papers:
- [Subtype Universes](http://www.cs.rhul.ac.uk/home/zhaohui/Subtype%20Universes.pdf)
- [Luo's thesis](http://www.cs.rhul.ac.uk/home/zhaohui/ECS-LFCS-90-118.pdf) (see here for [a book version of the thesis](https://global.oup.com/academic/product/computation-and-reasoning-9780198538356?cc=gb&lang=en&)) describes the type theory on which the above paper is based. It's called ECC and is a particular presentation of the Calculus of Constructions extended with coercive subtyping, described in
- [Coercive subtyping: Theory and implementation](https://hal.archives-ouvertes.fr/hal-01130574/document)

**Status: Coercions have been implemented in Coq for a long time. Universe cumulativity is semi-standard, as some proof assistant don't have it. Implicit coercions between primitive types are standard. Subtyping for records is standard in the languages that have "structural" record types. Subtyping of anything else in type theory is mostly wild speculations.**

TODO:
- Find out how subtype universes interact with records.

## Singleton Types <a id="singletons"></a> [↩](#toc)

TODO

Papers:
- TODO

**Status: TODO**

TODO:
- TODO

## [Type-level rewriting](Rewriting) <a id="type-level-rewriting"></a> [↩](#toc)

TODO!

The additional computational properties can be realized using rewrite rules, whose prototype is implemented in Agda. I'm not sure how rewrite rules interact with Agda's Prop, but I think this shouldn't be a problem.

We have made `Empty` and `Unit` into strict propositions to make our lives easier - nobody likes having to pattern match on `u : Unit` just to learn that it's equal to `unit` (what a surprise!), just as nobody likes having to infer that two proofs of `Empty` are equal from contradiction.

But since we are greedy type-theoretic bastards, we would like to have more computational equalities than that. So, `Empty` enjoys some special computational properties at the type-level and also the corresponding properties at the term level.

```
// `Empty` lives in the lowest predicative universe and at h-level 1
// (i.e. in the universe of strict propositions).
> :check Empty
> Empty : Type (h = 1, p = 0)
```

```
Sum-Empty-l : Empty + A = A := refl
Sum-Empty-l-inl (e : Empty) : (inl e : Empty + A) = (abort e : A) := refl
Sum-Empty-l-inr (a : A) : (inr a : Empty + A) = a := refl

Sum-Empty-r : A + Empty = A := refl
Sum-Empty-r-inl (a : A) : (inl a : A + Empty) = a := refl
Sum-Empty-r-inr (e : Empty) : (inr e : A + Empty) = (abort e : A) := refl
```



```
Prod-Empty-l : Empty * A = Empty := refl
Prod-Empty-l' (e : Empty) (a : A) : (e, a) = e := refl
Prod-Empty-l'' (x : Empty * A) : x = x.outl := refl

Prod-Empty-r : A * Empty = Empty := refl
Prod-Empty-r' (e : Empty) (a : A) : (a, e) = e := refl
Prod-Empty-r'' (x : A * Empty) : x = x.outr := refl
```

```
// These properties generalize to records.
// TODO: stating this property requires extensible records, which are experimental.
Record-Empty (R : RType) : (e : Empty & R) = Empty := refl

// These are not the only special computational properties of `Empty` - there's more:
Fun-Empty : Empty -> A = Unit := refl
Fun-Empty' (f : Empty -> A) : f = unit := refl

Path-Empty : (Empty = Empty) = Unit := refl

Nabla-Empty : (∇ α : A. Empty) = Empty := refl

Sub-Empty : Sub Empty = Unit := refl
Sub-Empty' (X : Sub Empty) (x : X) : x = unit := refl

Ref-Empty (P : Empty -> Prop) : {e : Empty | P e} = Empty := refl
```

```
// `Unit` lives in the lowest predicative universe and at h-level 0
// (i.e. in the universe of contractible types).
> :check Unit
> Unit : Type (h = 0, p = 0)
```

```
// `Unit` enjoys some special computational properties at the type level to
// make our lives easier.
Prod-Unit-l : Unit * A = A := refl
Prod-Unit-l' (u : Unit) (a : A) : (u, a) = a := refl

Prod-Unit-r : A * Unit = A := refl
Prod-Unit-r' (a : A) (u : Unit) : (a, u) = a := refl

// These properties generalize to records.
// TODO: stating this property requires extensible records, which are experimental.
Record-Unit-r (R : RType) : (u : Unit & R) = R := refl

// These are not the only special computational properties of `Unit` - there's more:
Fun-Unit-Dom : Unit -> A = A := refl
Fun-Unit-Dom' (f : Unit -> A) : f = f unit := refl

Fun-Unit-Cod : A -> Unit = Unit := refl
Fun-Unit-Cod' (f : A -> Unit) : f = unit := refl

Path-Unit : (Unit = Unit) = Unit := refl

Nabla-Unit : (∇ α : A. Unit) = Unit := refl

//Sub-Unit : Sub Unit = Bool := refl

Ref-Unit (P : Unit -> Prop) : {u : Unit | P u} = Unit := refl
```

```
// Some type-level computational properties of Paths.

Path-Prod (x y : A * B) : (x = y) = (outl x = outl y * outr x = outr y) := refl
Path-outl #(x y : A * B) (p : x = y) : outl x = outl y := outl p
Path-outr #(x y : A * B) (p : x = y) : outr x = outr y := outr p

// TODO: stating this property requires extensible records, which are experimental.
// `x removing a` is somewhat experimental too.
// The story for coinductives is probably similar.
Path-Rec (A : Type) (R : RType) (x y : (a : A & R)) :
  (x = y) = (a : x.a = y.a & x removing a = y removing a) := refl

Path-Fun (f g : (x : A) -> B x) : (f = g) = ((x : A) -> f x = g x) := refl
Path-app #(f g : (x : A) -> B x) (p : f = g) (x : A) : f x = g x := p x

Path-Empty (e1 e2 : Empty) : (e1 = e2) = Unit := refl

Path-Unit (u1 u2 : Unit) : (u1 = u2) = Unit := refl

// Also known as the Univalence Principle :)
Path-Type (A B : Type) : (A = B) = Equiv A B := refl

// Not sure about this one, but maybe.
Path-Path #(x y : A) (p q : x = y) : (p = q) = (path i j => p i = q j)

// The rest.
Path-Nabla (x y : ∇ α : A. B α) : (x = y) = ν α. x @ α = y @ α := refl
Path-concr #(x y : ∇ α : A. B α) (p : x = y) (α : Name A) : x @ α = y @ α := p @ α

Path-Ref (x y : {a : A | P a}) : (x = y) = (x ={A} y) := refl

Path-Sub #(A : Type) (X Y : Sub A) : (X ={Sub A} Y) = (X ={Type} Y) := refl


// Inductives are a bit more problematic. Usually it's easy to prove a characterization
// of paths using the encode-decode method, but stating how this will work in general is
// troublesome.
Path-Sum (x y : A + B) :
  (x = y) =
  match x, y with
  | inl a1, inl a2 => a1 = a2
  | inr b1, inr b2 => b1 = b2
  | _     , _      => Empty
  := refl

Path-inl (x y : A) : (inl x = inl y) = (x = y) := refl
Path-inr (x y : B) : (inr x = inr y) = (x = y) := refl
```

Of course we don't want to confine ourselves to just built-in computational equalities for `Empty` and `Unit` - we want to be able to define custom types with custom equalities of this kind. One way to do this is with rewrite rules.

Book:
- [Term Rewriting And All That](https://www21.in.tum.de/~nipkow/TRaAT/)

Papers:
- [Type Theory Unchained: Extending Agda with User-Defined Rewrite Rules](https://drops.dagstuhl.de/opus/volltexte/2020/13066/pdf/LIPIcs-TYPES-2019-2.pdf) (see section 2.6 for how to get rewriting rules for ordinary equality - if I read the paper correctly, it's also possible for Path types)
- [The Taming of the Rew: A Type Theory with Computational Assumptions](https://hal.archives-ouvertes.fr/hal-02901011v2/document)
- [The Multiverse: Logical Modularity for Proof Assistants](https://arxiv.org/pdf/2108.10259.pdf)

**Status: wild speculations.**

TODO:
- Everything.
- Find how these types will be declared.
- Make sure that it all makes sense.

## Tooling <a id="tooling"></a> [↩](#toc)

[The Unison Language](https://www.unisonweb.org/) has a very futuristic tooling and some good ideas, including:
- codebases - Unison code is literraly stored as an AST in a nice database managed with a dedicated tool
- everything can be referred to by its hash and names are just metadata, so its easy to rename stuff and perform other similar magic like caching tests
- Unison has typed documentation which prevents it from going out of sync with the code

## Missing features <a id="missing-features"></a> [↩](#toc)

This wishlist is not comprehensive. We could probably do better (i.e. have more nice things), but we have to stop somewhere, not to mention that all the interaction between all the different features blows the complexity of the language dramatically.

### Typed Holes

Holes are a way of leaving a part of a term unfilled as a kind of local "axiom". They can be later revisited with the help of the language's type inference, filled automatically or serve as names for goals in the proving mode. More ambitious works try to use holes for accomodating ill-typed, ill-formed and incomplete (yet unwritten) programs into the semantics.

TODO: Typed Holes have something to do with First-Class Patterns. And what if we could make typed holes first-class?

We would get, let's call them, Partial types - something like Singleton Types.

Examples:
1. `{x : nat ^^^ x = S (S ?n)}` - type of naturals that definitionally compute to `2 + something`. How do we compute with this? Dunno, but maybe `coe : {x : nat ^^^ _} -> nat`, with the rule `coe x => S (S ?n)`, whatever that means.
2. `{l : list A ^^^ l = []}` - singleton type of empty lists.
3. `{p : nat * nat ^^^ fst p = 42}` - type of pairs of naturals whose left component is definitionally equal to `42`, i.e. `fst (coe p) = 42`.
4. `{x : nat + bool ^^^ x = inr ?b}` - sum type of `nat` and `bool`, but its element are definitionally equal to `inr something`, so that `match coe x with | inl a => f a | inr b => g b end` computes to `g ?b`.
5. `{s : Stream nat ^^^ hd s = 42}` - type of streams whose head is `42`.
6. `{f : bool -> nat ^^^ f true = 42}` - type of functions from `bool` to `nat` that compute to `42` on `true`.
7. `{f : bool -> nat ^^^ f true = f false}` - type of definitionally weakly constant functions from `bool` to `nat`.
8. `{f : bool -> nat ^^^ f _ = 42}` - type of definitionally strongly constant functions that always returns `42`.
9. Maybe we need intersection and union types for this?

### Quantitative Type Theory

### Algebraic Effects