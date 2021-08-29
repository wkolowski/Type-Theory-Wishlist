# Type Theory Wishlist

This repo is a playground in which I'm trying to invent a better type theory/dependently-typed programming language. This README describes the core syntax and semantics of the language and points to some ideas and TODOs for later consideration. The details of every major feature/proposal are laid out in their respective directories, inside files with the `.ttw` extension that contain commented pseudocode which show the feature in action.

## The Guiding Principle of Syntax

The syntax of many ((dependently-typed) functional) languages is not optimal and sometimes not even good and, to be honest, the syntax of some of them (Coq) is horrible. We are not going to repeat their mistakes, however, by making use of a very simple principle used by programmers all over the world: Don't Repeat Yourself. To paraphrase: if we have to write something twice, the syntax is bad and has to be changed.

## Basic syntax

Comments start with `//` like in C.
```
// This is a comment.
```

Multiline comments are enclosed between ``(* *)`` like in the ML languages and can be nested. TODO: revisit this later.
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

## Types

| Name          | Formation        | Introduction     | Elimination      |
| ------------- | ---------------- | ---------------- | ---------------- |
| Function type | `(x : A) -> B x` | `fun x : A => e` | `f a`            |
| Universes     | `Type h p`       | `Type h p`       | can't eliminate  |
| Path type     | `x = y`          | `fun i : I => e` | `p i`            |
| Empty type    | `Empty`          | impossible       | `abort`          |
| Unit type     | `Unit`           | `unit`           | not needed       |
| Record types  | `(a : A, ...)`   | `(a => e, ...)`  | `p.x`            |
| Inductives    | see below        |
| Coinductives  | see below        |
| Nabla type    | `∇ α : A. B α`   | `ν α : A. e`     | `t @ α`          |

### Tentative

| Name          | Formation        | Introduction     | Elimination      |
| ------------- | ---------------- | ---------------- | ---------------- |
| Subtype type  | `Sub A`          | implicit (?)     | implicit (?)     |
| Refinements   | `{x : A \| P x}` | implicit (?)     | implicit (?)     |

## Functions

Function types work as usual.

```
add : (n m : Nat) -> Nat :=
  fun n m : Nat => ...
```

Of course we can also bind arguments together with the name, to the left of the final colon.

```
add (n m : Nat) : Nat := ...
```

Of course there is a mechanism of implicit arguments:

```
id {A : Type} (x : A) : A := x
```

Better syntax for implicit arguments (inspired by [the F* language](https://www.fstar-lang.org/)):

```
id (#A : Type) (x : A) : A := x
```

But we can also omit writing implicit arguments when they are easily inferable from something else (this piece of syntax is inspired by [Idris 2](https://idris2.readthedocs.io/en/latest/tutorial/typesfuns.html#implicit-arguments)). Example:

```
id (x : A) : A := x

comp (f : A -> B) (g : B -> C) (x : A) : C := g (f x)
```

We have a very concise way of defining functions by pattern matching:

```
half : Nat -> Nat
| z       => z
| s z     => z
| s (s n) => s (half n)
```

Besides these basics, we want to think that all functions take just one argument which is a big record (so not the usual "every function takes one argument, and then maybe returns another function").

### Parameters and indices

Arguments to the left of the colon are called parameters, the ones to the right are called indices. The difference is that parameters always stay the same, so that we don't need to write them explicitly. Indices can change, so we must write them explicitly.

It looks a bit weird for the map example below, but hey, you are going to appreciate it when the definitions get more complicated!

```
map (f : A -> B) : List A -> List B :=
| [] => []
| h :: t => f h :: map t
```

The distinction between parameters and indices has some other consequences too. For example, when defining additions of naturals, the most succinct definition forces us to do it by recursion on the second argument.

```
add (n : Nat) : Nat -> Nat :=
| z    => n
| s m => s (add m)
```

## Universes

We want to have a multidimensional hierarchy of universes stratified by both the usual predicative level and by homotopy level, similar to the [Arend language](https://arend-lang.github.io/about/arend-features#universe-levels). The predicative levels are basicaly naturals, whereas the homotopy levels are natural numbers extended with infinity (for untruncated types). The homotopy levels should bring some benefits, like you don't need to write some boring paths here and there (TODO: work out the details for the non-strict case).

Another possibility would be to make the homotopy levels strict, i.e. `Type (h = 0)` would be a universe of contractible types (whose member is itself), if only just for giggles. `Type (h = 1)` would then be a universe of strict (i.e. definitionally irrelevant) propositions (like Coq's [SProp](https://coq.inria.fr/refman/addendum/sprop.html) or Agda's [Prop](https://agda.readthedocs.io/en/v2.6.0/language/prop.html)), `Type (h = 2)` would be a universe of strict sets (types for which the type of paths is a strict proposition) and so on, up to `Type (h = ω)`, the universe of untruncated types.

Some reading on universes:
- [Definitional Proof-Irrelevance without K](https://hal.inria.fr/hal-01859964v2/document)
- [Generalized Universe Hierarchies and First-Class
Universe Levels](https://arxiv.org/pdf/2103.00223.pdf)
- [Notes on Universes in Type Theory](http://www.cs.rhul.ac.uk/home/zhaohui/universes.pdf)

TODO:
- Everything

## [Empty](TypesThatCompute/Empty.ttw), [Unit](TypesThatCompute/Unit.ttw) and [Types that Compute](TypesThatCompute)

`Empty` and `Unit` are a little special in that all their terms are computationally equal, i.e. they are strict propositions (this should be the case even if we don't manage to pull out the strict universes thing). But that's not the end - `Empty` and `Unit` also enjoy special computational properties:
- `Empty + A = A`
- `A + Empty = A`
- `Empty * A = Empty`
- `A * Empty = Empty`
- `Unit * A = A`
- `A * Unit = A`
- generalizations of the above to record
- corresponding properties at the term level
- similar properties for other type formers

Of course we don't want to confine ourselves to these built-in computational equalities - we want to be able but to define custom types with custom equalities of this kind. One way to do this is with rewrite rules. See [Type Theory Unchained: Extending Agda with User-Defined Rewrite Rules](https://drops.dagstuhl.de/opus/volltexte/2020/13066/pdf/LIPIcs-TYPES-2019-2.pdf) for more on rewrite rules.

TODO:
- List all the additional laws for `Empty` and `Unit`
- Make sure that it all makes sense

### [Path types and other cubical stuff](Paths)

We take Cubical Type Theory and the homotopical style of doing mathematics for granted. The revolution has already occurred!

But we also want to benefit from [Types that Compute](TypesThatCompute) when it comes to paths, i.e. we want path characterizations like "paths between pairs are pairs of paths" to hold by computation, without needing to prove anything. See [Type Theory Unchained: Extending Agda with User-Defined Rewrite Rules](https://drops.dagstuhl.de/opus/volltexte/2020/13066/pdf/LIPIcs-TYPES-2019-2.pdf) (section 2.6) for how to accomplish something like this for Agda's usual (i.e. inductive) equality. If I read the paper correctly, it's also possible for Path types.

TODO:
- Refresh my knowledge of and then master the machinery behind Cubical Type Theory (systems, Glue, etc.)

## [Records](Records)

Record types are the central feature of the language and they subsume modules, typeclasses, sigma types, product types, and so on.

Some reading on dependent records in type theory:
- [Dependent Record Types Revisited](http://www.cs.rhul.ac.uk/home/zhaohui/DRT11.pdf)
- [Typed Operational Semantics for Dependent Record Types](http://www.cs.rhul.ac.uk/home/zhaohui/TYPES09final11-01-01.pdf)
- [Extension of Martin-Löf's Type Theory with Record Types and Subtyping](https://www.researchgate.net/publication/2683061_Extension_of_Martin-Lof's_Type_Theory_with_Record_Types_and_Subtyping)

## Sum types

As for sum types, we would like to have extensible sum types, akin to OCaml's polymorphic variants. If that's not possible, then sum types are subsumed by inductive types.

## Inductive types

The different classes of inductive types (enumerations, parameterized types, inductive families, etc.) have progressively more complete syntaxes, so that simple types can be written in a simple way and only the more complicated ones require more details.

Enumerations can NOT be written in a single line and must have the initial bar.
```
data Bool : Type :=
| ff
| tt
```

The same distinction between parameters and indices also applies to inductive type definitions. Note that we also don't need to write the return type of the constructors because it's the same in every case.
```
data Option (A : Type) : Type :=
| None
| Some A
```

We can (and should) name the argument of each constructor, as this will be used for automatic name generation - something well known to be lacking in most proof assistant.
```
data List (A : Type) : Type :=
| Nil
| Cons (hd : A) (tl : List)
```

We can then use these names when definition functions.
```
app : (l1 l2 : List A) -> List A :=
| Nil , _ => l2
| Cons, _ => Cons l1.hd (app l1.tl l2)
```

But we don't need to:
```
app : (l1 l2 : List A) -> List A :=
| Nil     , _ => l2
| Cons h t, _ => Cons h (app t l2)
```

But there's an even shorter way to define this function: we can unpack the constructor's arguments in place to use their short names.
```
app : (l1 l2 : List A) -> List A :=
| Nil   , _ => l2
| Cons{..}, _ => Cons h (app t l2)
```

This `{..}` syntax is based on Haskell's [Record Wildcards](https://kodimensional.dev/recordwildcards), but it probably should be changed to something shorter. TODO: we should also consider what to do with `as`-patterns (Haskell's `@`-patterns).

Even better: we don't need to write `{..}` because records get opened/unpacked automatically.
```
app : (l1 l2 : List A) -> List A
| Nil , _ => l2
| Cons, _ => hd :: app tl l2
```

For inductive families, everything looks mostly similar to other languages (except that we still don't need to write the parameters!).
```
data Vec (A : Type) : Nat -> Type :=
| Nil  : Vec 0
| Cons : (hd : A) {n : Nat} (tl : Vec n) -> Vec (s n)
```

Inductive types are supposed to be really powerful. We take the usual inductive families as baseline and add:
- [Induction-Induction](IndInd)
- Induction-Recursion
- [Nominal Inductive Types](Nominal)
- [Higher Inductive Types](Paths)
- [Constructors that Compute](ConstructorThatCompute)
- [Overlapping and Order-Independent Patterns](OverlappingPatterns)
- [Decidable Equality Patterns](DecidableEqualityPatterns)

## Coinductive types

Coinductives should be dual to inductives, but that will be hard to achieve as they are underresearched. The minimum is to have a nice syntax sugar for "positive" coinductive types (like the coinductive duals of natural numbers and lists). Another possibility for handling coinductives is for them to be just (co)recursive records, but this depend on how cool and foreign records will be.

It would be nice to have a compact syntax for coinductive types. Let's try some crazy `&`s!

```
codata Stream (A : Type) : Type :=
& hd : A
& tl : Stream
```

We could then use copattern matching to define functions:

```
interleave (l r : Stream a) : Stream a :=
& hd    => l.hd
& hd tl => r.hd
& tl tl => interleave l.tl r.tl
```

So far so good, but what about coinductive lists, conatural numbers and other single-field coinductives? We shall have a syntax sugar for that! Example:

```
codata CoList (A : Type) : Type :=
| CoNil
| CoCons (hd : A) (tl : CoList)
```

The above is neither an inductive type nor a "positive" coinductive type. It is just a syntax sugar to represent something like this:

```
data CoListX (X A : Type) : Type :=
| CoNilX
| CoConsX (hd : A) (tl : X)

codata CoList (A : Type) : Type :=
& Out : CoListX CoList A

CoNil : CoList a :=
& Out => CoNilX

CoCons (h : a) (t : CoList a) : CoList a :=
& Out => CoConsX h t
```

See [this file](OverlappingPatterns/Conat.ttw) for more details on this notation.

### [Nabla types and names](Nominal)



| Path type     | `x = y`          | `fun i : I => e` | `p i`            |
| Nabla type    | `∇ α : A. B α`   | `ν α : A. e`     | `t @ α`          |
| Subtype type  | `Sub A`          | implicit (?)     | implicit (?)     |
| Refinements   | `{x : A \| P x}` | implicit (?)     | implicit (?)     |

### Refinements

Turns out F* has some nice features that would be nice to have here too:
- Discriminators that check which constructor was used to make the given term, e.g. `Nil? : list 'a -> bool`, `Cons? : list 'a -> bool`
- Projections which project constructor arguments out of a term (given that the term was really made using that constructor): `Cons?.hd : l : list 'a{Cons? l} -> 'a`, `Cons?.tl : l : list 'a{Cons? l} -> list 'a`
- Note that the above are written in F* syntax and require refinement types to get anywhere.

## Subtyping

It would be nice to have subtyping, but it's hard to say how easy (or hard) it is to achieve in a dependently-typed setting.

The subtyping judgement shall be proof-relevant, i.e. it should explicitly specify the coercion used to pass from the subtype to the supertype. These coercions should be unique, i.e. there can't be two coercions from `A` to `B`. It should also be possible to declare custom coercions.

TODO: cite Luo.

Subtyping for universes is simple. We have `c : U_i <= U_j` whenever `i <= j` and the coercion `c` is a trivial lift.

Subtyping for records is a bit complicated. See [this file](Records/TurboRecords.ttw).

Subtyping for functions is contravariant, i.e. `A <= A'` and `B <= B'` implies `A' -> B <= A -> B'`.

We could make `abort : Empty -> A` and `delete : A -> Unit` into coercions if we wanted.

For sums, we basically have `A <= A + B` and `B <= A + B`.

Not sure about subtyping for inductives and coinductives.

For subtype universes, we have `A <= B` implies `Sub A <= Sub B`.

For refinement types, we have `{x : A \| P x} <= A`.

For nablas, we should have `A <= A'` and `B <= B'` implies `∇ α : A. B α <= ∇ α : A'. B' α`.

For paths types, I think `I` is invariant, so given `c : A <= B` and `p : x ={A} y` we have `fun i : I => c (p i) : c x ={B} c y`

## Things to investigate

### Turning contexts into record types

How to turn typing contexts into record types so that we can have records in the language for free.

Beware! This is not the same idea as "first-class typing contexts" and certainly not the same as "first-class evaluation contexts".

### Global definitions/declarations

Global definitions are those that can appear in the typing context, as opposed to local definitions which can be represented by let-bindings and ultimately as just functions. Global definitions could be useful in investigating record types with already-set fields.

### Bidirectional typechecking

Bidirectional typechecking is a way of presenting the typing rules that is more algorithmic and thus better suited for implementation. It is also said to increase the quality of error messages. But most importantly, putting rules into the bidirectional format makes them less fishy.

### Typed holes

Holes are a way of leaving a part of a term unfilled as a kind of local "axiom". They can be later revisited with the help of the language's type inference, filled automatically or serve as names for goals in the proving mode. More ambitious works try to use holes for accomodating ill-typed, ill-formed and incomplete (yet unwritten) programs into the semantics.

### Typed documentation

Documentation is well known for its tendency to go out of sync with the code. So maybe it's time to make it strongly-typed?

See [the Unison Language](https://www.unisonweb.org/) for more on typed documentation.

### Explicit substitutions

Another way to make the presentation of your type theory less fishy, more concrete and down-to-earth and more amenable to implementation.

### Normal forms

How to infer, in general, an inductive characterization of normal forms from the reduction relation?

### The status of primitive constants

Primitive constants are used to include in type theory various types known from more mainstream languages, like ints, floats, arrays, etc.

### Refinement types

The idea is to have, for a type T, lots of its subtypes of the form {x : T | P} where P is some decidable property that the typechecker can reason about.

See:
- F* language - refinements types work pretty well here and are very useful.