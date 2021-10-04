# Things to investigate

## Global definitions/declarations

Global definitions are those that can appear in the typing context, as opposed to local definitions which can be represented by let-bindings and ultimately as just functions. Global definitions could be useful in investigating record types with manifest fields.

## Bidirectional typechecking

Bidirectional typechecking is a way of presenting the typing rules that is more algorithmic and thus better suited for implementation. It is also said to increase the quality of error messages. But most importantly, putting rules into the bidirectional format makes them less fishy.

## Explicit substitutions

Another way to make the presentation of your type theory less fishy, more concrete and down-to-earth and more amenable to implementation.

## Normal forms

How to infer, in general, an inductive characterization of normal forms from the reduction relation?