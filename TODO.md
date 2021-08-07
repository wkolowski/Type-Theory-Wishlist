# Things to investigate

## First-class typing contexts.

How to turn typing contexts into record types so that we can have records in the language for free.

## Global definitions/declarations

Global definitions are one that can appear in the typing context, as opposed to local definitions which can be represented by let-bindings and ultimately as just functions. Global definitions could be useful in investigating record types with already-set fields.

## Bidirectional typechecking

Bidirectional typechecking is a way of presenting the typing rules that is more algorithmic and thus better suited for implementation. It is also said to increase the quality of error messages. But most importantly, putting rules into the bidirectional format makes them less fishy.

## Typed holes

Holes are a way of leaving a part of a term unfilled as a kind of local "axiom". They can be later revisited with the help of the language's type inference, filled automatically or serve as names for goals in the proving mode. More ambitious works try to use holes for accomodating ill-typed, ill-formed and incomplete (yet unwritten) programs into the semantics.

## Typed documentation

Documentation is well known for its tendency to go out of sync with the code. So maybe it's time to make it strongly-typed?

See:
- Unison language

## Explicit substitutions

Another way to make the presentation of your type theory less fishy, more concrete and down-to-earth and more amenable to implementation.

## Normal forms

How to infer, in general, an inductive characterization of normal forms from the reduction relation?

## The status of primitive constants

Primitive constants are used to include in type theory various types known from more mainstream languages, like ints, floats, arrays, etc.

## Refinement types

The idea is to have, for a type T, lots of its subtypes of the form {x : T | P} where P is some decidable property that the typechecker can reason about.

See:
- F* language - refinements types work pretty well here and are very useful.