# Universes

We denote the strict universes by `SType h p`. We can be more explicit by writing `SType (h = h', p = p')`. We allow "typical ambiguity", i.e. when the level is not written, it will be inferred and solved by the universe checker. We can be more explicit and ambiguous at once, for example writing `SType (h = h')` - the homotopy level is explicit, but the predicative level will be inferred. We abbreviate `SType (h = 0)` with `SContr`, `SType (h = 1)` with `SProp`, `SType (h = 2)` with `SSet` and `SType (h = 3)` with `SGrpd`.

Ordinary (non-strict) universes follow the same conventions, except that they are called `Type` and the abbreviations for the various h-levels are `Contr`, `Prop`, `Set` and `Grpd`, respectively.

We will use Russell style universes because they are easier to read and write. Subtyping for universes states that `SType h p <= SType h' p'` whenever `h <= h'` and `p <= p'` and similarly for `Type`. Additionally we have `SType h p <= Type h p`, i.e. we may go from a strict universe to a non-strict one, but not the other way around.

Idea: maybe merge these into one, i.e. `Type s h p`, with `s` being the strict level, `h` the homotopy level and `p` the predicative level? Of course we will then have `h <= s`.

## Levels

The predicative levels are natural numbers and the homotopy levels are natural numbers extended with infinity (written `ω` or `oo`). Operations on levels include `pred` and `max`, defined as follows:

```
pred 0 = 0
pred (l + 1) = n
pred oo = oo
```

```
max 0 l = l
max l 0 = l
max (l1 + 1) (l2 + 1) = s (max l1 l2)
max oo l = oo
max l oo = oo
```

## Rules for `=`/`Path`

The basic idea is that of `A : SType h p` and `x y : A`, then `x = y : SType (pred h) p` and similarly for `Type` (from now we will omit `Type` and concern ourselves only with `SType`). How this looks in practice:

```
// This holds because all proofs of a strict proposition are equal.
isProp-from-SProp {A : SProp} (x y : A) : x = y := refl
```

```
// `A : SSet`, so `x = y : SProp` and so trivially `p = q`.
isSet-from-SSet {A : SSet} {x y : A} (p q : x = y) : p = q := refl
```

```
// Analogously for strict groupoids.
isGrpd-from-SGrpd {A : SGrpd} {x y : A} {p q : x = y (r s : p = q)
  : r = s := refl
```

And so on. Simple, isn't it?

## Rules for other types

| Name          | Rule             |
| ------------- | ---------------- |
| Universes     | `SType h p : SType (h + 1) (p + 1)` |
| Path type     | if `A : SType h p` <br> and `x y : A` <br> then `x = y : SType (pred h) p` |
| Function type | if `A : SType h1 p1` <br> and `B x : SType h2 p2` <br> then `(x : A) -> B x : SType h2 (max p1 p2)`  |
| Empty type    | `Empty : SProp`  |
| Unit type     | `Unit : SContr`  |
| Record types  | if `A_i : SType h_i p_i` <br> then `(a_i : A_i) : SType (max h_i) (max p_i)` |
| Inductives    | see below        |
| Coinductives  | see below        |
| Name type     | if `A : SType h p` <br> then `Name A : SType 2 p` |
| Nabla type    | if `B α : SType h p` <br> then `∇ α : A. B α : SType h p` |
| Refinements   | if `A : SType h p` <br> and `P : A -> SProp` <br> then `{x : A \| P x} : SType h p` |
| Subtypes      | if `A : SType h p` <br> then `Sub A : SType (max 2 h) p` |

## Restrictions

What are the restrictions on elimination of strict types and so on? In Coq and Agda there's a restriction on elimination of strict propositions so as to avoid "spilling" the strictness into the outside world, which could result in nontermination, undecidability of type checking and falling into extensional type theory.

This restrction says that (inductive) strict propositions can be eliminated into ordinary `Type`s if they satisfy some simple critera, which in practice amount to saying that all strict propositions which can be eliminated are built from `Empty`, `Unit` and recursive functions which return either `Empty` or `Unit`.

For us, this means that `Empty` and `Unit` can be eliminated into anything at all and that other strict propositions can be eliminated only into other strict propositions. At higher h-levels this generalizes to the criterion that `SType h p` can be eliminated only into `SType h' p'` where `h' <= h`. For example, we can eliminate strict sets into strict sets and strict propositions (and `SContr`), but not into strict grupoids or non-strict types.

## Inductives, coinductives, truncations - TODO