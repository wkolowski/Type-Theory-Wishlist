# Some problems with records found in most languages

Most languages have lots of problems with records:
0. Besides records we have typeclasses with instance search, modules which are even more second-class than records and sigma types which are just annoying. Additionally, in the metatheory we also have contexts, which are basically just another form of records. Moreover, record definitions are pretty similar to definition of (non-inductive) sums, inductives and coinductives, in the sense that all of these are just a bunch of `name : type` declarations.
1. Record field names must be globally unique. This is very annoying in Haskell and Coq, but probably easy to solve and not present in other languages.
2. No definitional uniqueness principle for records in most languages. This is solved in Agda, however.
3. Hard to prove record equality. This is very annoying in Coq, but probably much easier when we have Cubical Type Theory and path types.
4. Hard to reuse record types. For example, when we have record types that represent reflexive, symmetric and transitive relations, they aren't very helpful when defining a record type for equivalence relations - if we try to reuse them, we'll get a subpar solution.
5. Telescopization stemming from lack of inheritance. In an extreme version of the algebraic hierarchy, a group is a monoid with inverse, and a monoid is a pointed semigroup with laws, and a semigroup is an associative magma and so on. Defining a group then requires unwinding all these telescopes, which is unwieldy.
6. Hard to unbundle records into typeclasses (i.e. turn a `Monoid` into an instance of `Monoid A` for some carrier `A`) and hard to bundle classes into records (i.e. turn an instance of `Monoid A` into a `Monoid` whose carrier is `A`).
7. This is not directly about records, but it's sometimes hard to do currying of functions that take many arguments. Records could help wiht that, but they don't, because we don't have any notion of "partial application" for records.


# A partial solution: First-Class Record Types

The state of records in Coq and generally in almost every possible language is sad, even though it could be better.

The problem with records is that _record types_ are second-class citizens. To be more precise, they exist in the metalanguage (you can talk about them in English), but they don't exist in the object language - you can't say that a particular type is a record type or that something holds for all record types, even though there is a record mechanism which allows defining new types.

From that follows a lot of inconveniences that could be eliminated if record types were first-class. But what does that mean?

Well, there should exist an inductive type, which we will call `Rec` in this note, whose elements were codes that could be interpreted as record types.

For example, the record type below (in Coq syntax):

```coq
Record Sigma (A B : Type) : Type :=
{
    outl : A;
    outr : B;
}.
```

could be an interpretation of the following code:

```coq
Field "outr" B (Field "outl" A Nil)
```

The details of the universe of codes are left to our imagination, although if the language has induction-recursion, it can be used to define such a universe like so:

```coq
Inductive Rec : Type :=
    | RNil : Rec
    | RCons :
        forall {R : Rec} {P : El R -> Type} {x : El R},
            string -> P x -> Rec
```

where `El` is the function that interprets the codes as actual record types.

We won't pay much attention to formal details in this note. What nice things can we achieve with such record types? Here's a short list (to make our lives easier, we will use concrete syntax of record types instead of codes):
- Subtyping. Given two record types we can easily check whether one is a subtype of the other. For example `R = {x : nat, y : bool, z : True}` is a subtype of `R' = {x : nat, y : bool}`, so `R` can be easily coerced to `R'`, just by forgetting the field `z`.
- Setting a value. We can make record types with some fields set in advance to a given value. Let `R = {x : nat, y : bool, z : True}`. We could write for example `R with x = 42` and get the record type `{x = 42 : nat, y : bool, z : True}`, whose values are the same records as for the record type `{y : bool, z : True}`. It's a kind of "partial application" for records and record types.
- Changing name of a field. We can change the name of a field to one which is more convenient in a given situation. Let `R = {x : nat, y : bool}`. Then we can write `R renaming (x to n, y to b)` and get the record type `{n : nat, b : bool}`.
- Union. We can take the union of two record types with duplicating fields that have the same names and types. Example: if `R = {x : nat, y : bool}` and `S = {x : nat, z : True}`, then `R ∪ S = {x : nat, y : bool, z : True}`.
- Intersection. Analogous to union. Example: `R ∩ S = {x : nat}`.
- Extension. An operation similar to taking an union with a single field record type. Example: `{x : nat, y : bool} with z : True = {x : nat, y : bool, z : True}`.
- Deletion of a field. Example: `{x : nat, y : bool, z : True} \ z = {x : nat, y : bool}`.

Which problems are solved by all these nice enhancements? Well, a few of them. Let's define some example record types first. Let

```
Refl =
{
    A : Type,
    R : A -> A -> Prop,
    refl : forall x : A, R x x
}

Sym =
{
    A : Type,
    R : A -> A -> Prop,
    sym : forall x y : A, R x y -> R y x
}

Trans =
{
    A : Type,
    R : A -> A -> Prop,
    trans : forall x y z : A, R x y -> R y z -> R x z
}
```

These are of course record types that represent reflexive, symmetric and transitive relations, correspondingly.

The first problem of records in Coq is that it's hard to convert them to classes. Given `Refl` like above, turning it into the type of reflexive relations on natural numbers makes us write something like `{R : Refl | A R = nat}`, which is super inelegant and from the univalent point of view incorrect (there's hell a lot of paths `R = nat`). Conversion in the other direction, from class to record, is very boilerplatey and boils down to redefining the type from scratch. Example:

```coq
Definition isReflexive
    {A : Type} (R : A -> A -> Prop) : Prop :=
        forall x : A, R x x.

Definition Refl : Type :=
{
    A : Type;
    R : A -> A -> Prop;
    refl : isReflexive R;
}.
```

Not nice, eh? Particularly when our record types has a lot of fields - the waste of time for writing boilerplate is enormous. This problem is solved by setting field values in record types. With such a convenience we can get the type of reflexive relations on natural numbers by writing `Refl with A = nat`, and `isReflexive` can be defined like so: `isReflexive A' R' = Refl with A = A', R = R'`.

Thanks to this mechanism we have a canonical way of representing all possible related concepts at once: a reflexive relation, being a reflexive relation, etc. Of course boilerplate is still present, so one could attempt to autogenerate all these things, for example by positing that each field corresponds to a subtype of the original record type comprised of this field and all the fields it depends on.

Moreover, these enhanced record types not only unify Coq's records and classes, but also Coq's modules. They are even much more powerful than them, because they allow changing field names and so on.

The second problem of Coq records is an extreme degree of telescopization. The point is that intuitively e.g. a group is a monoid with inverses, whereas formally in Coq a group is a record that has the monoid as a field and the other fields are the inverse and the appropriate laws.

It's a problem, because with a few such nestings, to define a record we need to write `x := { y := { z := {w := { ...}}}}` and so on, which is very bad. Thanks to enhanced record types we can prevent this by writing simply that the type of groups is simply the union of the type of monoids, the inverse and laws.

![Grupa](records2.jpg)

The third problem is that it's hard to reuse Coq record types. For example, to define the type of equivalence relations, we need to write something like this:

```coq
Record Equiv : Type :=
{
    A : Type;
    R : A -> A -> Prop;
    refl : forall x : A, R x x;
    sym : forall x y : A, R x y -> R y x;
    trans : forall x y z : A, R x y -> R y z -> R x z;
}.
```

![Equiv](records.jpg)

Of course it's a bit boilerplatey if we need to define reflexive, symmetric and transitive relations separately. With enhanced record types, we could simply use an union, writing `Equiv = Refl + Sym + Trans`.

The fourth problem is a whole bunch of inconveniences with functions. First and foremost, it's hard to partially apply a function, particularly when it takes a lot of arguments. Let's see a few stages of a function's evolution:
- `f : A * B * C -> D` - we can perceive `f` as a function of "many variables". The domain is represented with a product. Partial application is hard, because we need to write e.g. `fun p : A * B => f (outl p, outr p, c)`
- `f : A -> B -> C -> D` - we can perceive `f` as a function of a "single variable", curried. Partial application is easier than before: `f a`. Well, unless we want to partially apply one of the further arguments, then it's not easier at all: `fun a b => f a b c`. The farther the argument. the more boilerplate.
- `f : {x : A, y : B, z : C} -> D` - a function which takes all its inputs packed into an enhanced record. Partial application is easy for every argument, we (would) only need to write something like `f {z = c}`, to get a function of type `{x : A, y : B} -> D`.

At the same time such a representation of functions hits more birds with one stone: we have named arguments, optional arguments, default arguments, implicit arguments, etc. Moreover, if inductive types' constructor take arguments packed in such enhanced records, we get for free a whole bunch of convenient notations described in the note on [Syntax](../Core/Syntax.md).

## Is it even possible?

Can record types as described above even be implemented? I don't know, but I think all of that isn't as difficult as it seems, because everything boilds down to operations on codes, and a universe of codes can be defined in a language that supports induction-recursion, like Agda. Moreover, there are some papers describing universes of codes for inductive types, even ones which have a code for the universe itself, and they pose no problems.