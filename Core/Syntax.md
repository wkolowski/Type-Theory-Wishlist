# Guiding principle

The syntax of many ((dependently-typed) (functional)) languages is not optimal and, to be honest, the syntax of some of them (Coq) is horrible. We are not going to repeat their mistakes, however, by making use of a very simple principle used by programmers all over the world: Don't Repeat Yourself. To paraphrase: if we have to write something twice in the syntax, the syntax is bad and has to be changed.

## Basics

We always use ```=>``` to mean that the thing on the left computes to the thing on the right.

|       |              |                |             |
|-------|--------------|----------------|-------------|
| Name  | Formation    | Introduction   | Elimination |
| Function type | ```(x : A) -> B x``` | ```fun x : A => e``` <br> ```\x : A => e``` | ```f a``` |
| Empty type | ```Empty``` | | pattern matching |
| Unit type | ```Unit``` | ```unit``` | pattern matching |
| Product types | ```A * B``` | ```(a, b)``` | ```outl, outr``` <br> and also pattern matching |
| Sum types | ```A + B``` | ```inl, inr``` | pattern matching |



Definitions look like below. No keywords or anything like that - they are useless clutter.
```
name : type :=
  ...
```

Example:
```
answer : Nat := 42
```

For functions, we can of course bind arguments together with the name, to the left of the final colon.

Examples:

```
add (n m : Nat) : Nat := ...
```

There of course is a mechanism of implicit arguments:

```
id {A : Type} (x : A) : A := x
```

But we can also omit writing implicit arguments when they are easily inferable from something else. Example:

```
id (x : a) : a := x

comp (f : a -> b) (g : b -> c) (x : a) : c := g (f x)
```

## Parameters and indices

Arguments to the left of the colon are called parameters, the ones to the right are called indices. The difference is that parameters always stay the same, so that we don't need to write them explicitly. Indices can change, so we must write them explicitly. Examples:

It looks a bit weird for the map example below, but hey, you are going to appreciate it when the definitions get more complicated!
```
map (f : a -> b) : List A -> List B :=
| [] => []
| h :: t => f h :: map t
```

The distinction between parameters and indices has some other consequences too. For example, when defining additions of naturals, the most succinct definition forces us to do it by recursion on the second argument.
```
add (n : Nat) : Nat -> Nat :=
| z    => n
| s m => s (add m)
```

## Inductives

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
    | Cons (hd : A) (tl : list)
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

For inductive families, everything looks mostly similar to other languages (except that we still don't need to write the parameters!).
```
data Vec (A : Type) : Nat -> Type :=
| Nil  : Vec 0
| Cons : (hd : A) {n : Nat} (tl : Vec n) -> Vec (s n)
```

## Coinductives

It would be nice to have a similarly compact syntax for coinductive types. Let's try some crazy `&`s!

```
codata Stream (A : Type) : Type :=
& hd : A
& tl : Stream
```

We could then use "copattern" matching to define functions:

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

See the file OverlappingPatterns/Conat for more details.

## F* inspired goodies

Turns out F* has some nice features that would be nice to have here too:
- Discriminators that check which constructor was used to make the given term, e.g. `Nil? : list 'a -> bool`, `Cons? : list 'a -> bool`
- Projections which project constructor arguments out of a term (given that the term was really made using that constructor): `Cons?.hd : l : list 'a{Cons? l} -> 'a`, `Cons?.tl : l : list 'a{Cons? l} -> list 'a`
- Note that the above are written in F* syntax and require refinement types to get anywhere.