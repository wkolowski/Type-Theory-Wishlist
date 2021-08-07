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
plus (n m : Nat) : Nat := ...
```

There of course is a mechanism of implicit arguments, but we can also just omit writing them. Examples:

```
id (x : a) : a := x

comp (f : a -> b) (g : b -> c) (x : a) : c := g (f x)
```
## Parameters and indices