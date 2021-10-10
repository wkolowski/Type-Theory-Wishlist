# Things to investigate

## Global definitions/declarations

Global definitions are those that can appear in the typing context, as opposed to local definitions which can be represented by let-bindings and ultimately as just functions. Global definitions could be useful in investigating record types with manifest fields.

## Bidirectional typechecking

Bidirectional typechecking is a way of presenting the typing rules that is more algorithmic and thus better suited for implementation. It is also said to increase the quality of error messages. But most importantly, putting rules into the bidirectional format makes them less fishy.

## Explicit substitutions

Another way to make the presentation of your type theory less fishy, more concrete and down-to-earth and more amenable to implementation.

## Normal forms

How to infer, in general, an inductive characterization of normal forms from the reduction relation?

## What is this?

Let's call this Partial types - something like Singleton Types, but it also has something to do with (first-class?) patterns and refinement types.

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