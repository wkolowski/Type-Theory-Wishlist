# Coinduction-recursion?

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

The desugaring is pretty self-explanatory. It also shows us the limits of "positive" coinduction-recursion: we can mutually define dependent coinductive types and **non-recursive** functions defined by pattern matching. Recursive functions, however, are not allowed, because the inductive part of our desugaring is non-recursive, i.e. it is only one layer deep. Therefore, recursion is illegal in this case. This shouldn't be surprising - after all, defining recursive function by pattern matching on a coinductive argument is very illegal.

# Coinduction-coinduction?

What about "coinduction-coinduction" or something like that? Is it possible? Let's find out by defining infinite binary heaps again, but using only induction-induction syntax.

```
codata BHeap (R : A -> A -> Prop) : Type
| E
| N (v : A, l r : BHeap, okl : OK v l, okr : OK v r)

and OK (R : A -> A -> Prop) (v : A) : BHeap R -> Prop
| OK-E : OK E
| OK-N : (x : A) (l r : BHeap R) -> R v x -> OK (N x l r)
```

This desugars as follows.

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


# Coinduction-induction?