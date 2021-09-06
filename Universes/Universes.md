# Universes

## Idea

We want our universes to keep track of types' homotopy levels. This could:
- Give us more computational equalities by explicitly marking types as "strict propositions" (no computational content, i.e. all terms computationally equal), "strict sets" (paths are strict propositions) and so on. We call universes that are capable of this **strict universes**.
- Free us from boilerplate stemming from having to pass around proofs of being a proposition (`isProp`), a set (`isSet`) and so on and having to use them where appropriate. We call universes that are capable of this **non-strict** universes.

## Syntax

We denote the strict universes by `Type h p`. We can be more explicit by writing `Type (h = h', p = p')`. We allow "typical ambiguity", i.e. when the level is not written, it will be inferred and solved by the universe checker. We can be more explicit and ambiguous at once, for example writing `Type (h = h')` - the homotopy level is explicit, but the predicative level will be inferred. We abbreviate `Type (h = 0)` with `Contr`, `Type (h = 1)` with `Prop`, `Type (h = 2)` with `Set` and `Type (h = 3)` with `Grpd`.

Non-strict universes follow the same conventions, except that they are called `hType` and the abbreviations for the various h-levels are `hContr`, `hProp`, `hSet` and `hGrpd`, respectively.

We use Russell style universes because they are easier to read and write.

## Levels

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

## Basic mechanics of strict universes

The base case of our strict universe hierarchy is h-level 1, i.e. the universe of strict propositions. It's implementation is described in [Definitional Proof-Irrelevance without K](https://hal.inria.fr/hal-01859964v2/document).

```
// All proof of a strict proposition are computationally equal.
isProp-from-SProp (#A : Prop) (x y : A) : x = y := refl
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

## Basic mechanics of non-strict universes

The typing rules for non-strict universes are analogous to those for strict universes, but the benefits are somewhat different - they amount to not needing to handle some cases when defining function by patterns matching whose domain is known to be of some h-level.

This is because to define a function into an `n`-type, we only need to handle constructors of dimension less than or equal to `n - 1`. For example, when the codomain is a set, we only need to consider point constructors (obviously) and path constructors (so that we don't disconnect points which were connected), but not 2-dimensional path constructors (as all 2-paths in a set are contractible).

These benefits multiply enormously when matching two or more values. For example, proving a property of two elements of a [free group defined like this](../Induction/HIT/FG.ttw) requires only 9 cases instead of 49.

## Typing rules

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

## Truncation

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

## Restrictions on elimination of strict propositions

In Coq and Agda there's a restriction on elimination of strict propositions so as to avoid "spilling" the strictness into the outside world, which could result in nontermination, undecidability of type checking and falling into extensional type theory.

This restrction says that inductive strict propositions can be eliminated into ordinary `Type`s if they satisfy some simple critera, which in practice amount to saying that all strict propositions which can be eliminated are built from `Empty`, `Unit` and recursive functions which return either `Empty` or `Unit`. For us, this means that `Empty` and `Unit` can be eliminated into anything at all and that other strict propositions can be eliminated only into other strict propositions.

## Cumulativity

We cannot have cumulativity between strict propositions and larger universes in order to obey the restrictions on elimination. For now this means there's cumulativity between `Contr` and `Prop`, then a GIANT WALL, and then cumulativity starts again from strict sets upwards. So we have `Type 0 p <= Type h p'` for `h = 0` or `h = 1` and `p <= p'`, then a GIANT WALL, and then `Type (2 + h) p <= Type (2 + h') p'` for `h <= h'` and `p <= p'`. Similar rules hold for `hType`.

Additionally we have `Type (2 + h) p <= hType (2 + h) p`, i.e. we may go from a strict universe to a non-strict one if we are at or above the set level, but not the other way around...

## Restriction on elimination of other strict inductive types

What are the restrictions on elimination of strict inductive types at or above the strict set level?

At higher h-levels the criterion for strict propositions generalizes to the criterion that `Type h p` can be eliminated only into `Type h' p'` where `h' <= h`. For example, we can eliminate strict sets into strict sets and strict propositions (and `SContr`), but not into strict grupoids or non-strict types.

But is this really hte case? This would mean that we can't define a type family whose domain are the strict natural numbers. Yuck!

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

## TODO

I have no idea what I'm doing. If something is not described here, it defaults to how it works in [Arend](https://arend-lang.github.io/about/arend-features#universe-levels)

Idea: maybe merge strict and non-strict universes these into one, i.e. `Type s h p`, with `s` being the strict (homotopy) level, `h` the (non-strict) homotopy level and `p` the predicative level? Of course we will then have `h <= s`.
