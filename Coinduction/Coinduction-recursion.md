# Coinduction-recursion? Not really.

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

The desugaring is pretty self-explanatory. We define `BHeapX` and `OKX` by induction-recursion and then tie the knot by defining `BHeap` coinductively as the fixpoint of `BHeap` and `OK` as a wrapper around `OKX`.

The limits of "positive" coinduction-recursion seem to be pretty clear: we can mutually define dependent types coinductively and **non-recursive** functions by pattern matching. Recursive functions, however, are not allowed, because the inductive part of our desugaring is non-recursive, i.e. it is only one layer deep. Therefore, recursion is illegal in this case. This shouldn't be surprising - after all, defining recursive function by pattern matching on a coinductive argument is very illegal.

To sum up: there's no coinduction-recursion, but we can mutually define types coinductively and functions by pattern matching.

# Coinduction-coinduction? Not really.

What about "coinduction-coinduction" or something like that? Is it possible? Let's find out by defining infinite binary heaps again, but using only induction-induction syntax.

```
codata BHeap (R : A -> A -> Prop) : Type
| E
| N (v : A, l r : BHeap, okl : OK v l, okr : OK v r)

and OK (R : A -> A -> Prop) (v : A) : BHeap R -> Prop
| OK-E : OK E
| OK-N : (x : A) (l r : BHeap R) -> R v x -> OK (N x l r)
```

This definition too is a modification of the original inductive-inductive definition of finite binary heaps, so it's probably correct. The only difference is the use of the `codata` keyword. This desugars as follows.

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

Again, the desugaring looks pretty easy to grasp. `BHeapX` and `OKX` are defined by induction-induction, which is perfectly legal, even though there isn't a lot of induction going on and we could have used ordinary inductive families. Finally, we define `BHeap` by tying the knot and implement `OK` as a wrapper around `OKX`.

From this example it is obvious that there really isn't any coinduction-coinduction going on - it depicts only coinduction-induction, and the "induction" part isn't really that much inductive, as its only one layer deep. But contrary to what was the case for "coinduction-recursion", I don't see why the inductive part of a coinductive-inductive definition couldn't be truly inductive. Maybe we should look for a better example. Also, coinduction-coinduction still seems possible, at least when both types are "positive" coinductives.

# Coinduction-induction?

STREAM PROCESSORS!

```
mutual
  codata SP (A B : Type) : Type
  | Put (hd : B, tl : SP A B)
  | Get (gsp : A -> GetSP A B)

  data GetSP (A B : Type) : Type
  | Put (hd : B, tl : SP A B)
  | Get (g : A -> GetSP A B)
```

```
toStream : (f : SP A B) (s : Stream A) -> Stream B
& hd
  | Put => f.hd
  | Get => head (f.gsp s.hd) s.tl
& tl
  | Put => toStream f.tl s             // s.tl?
  | Get => tail (f.gsp s.hd) s.tl

and
head : (g : GetSP A B) (s : Stream A) -> B
| Put => g.hd
| Get => head (g.g s.hd) s.tl

and
tail : (g : GetSP A B) (s : Stream A) -> Stream B
| Put => g.tl
| Get => tail (g.g s.hd) s.tl
```

We have to interpret the definitions below as corecursive for `toStream` and recursive for `toStream'`.

```
toStream : (f : SP A B) (s : Stream A) -> Stream B
| Put
  & hd => f.hd
  & tl => toStream f.tl s
| Get => toStream' f.g s

and
toStream' : (g : GetSP A B) (s : Stream A) -> Stream B
| Put
  & hd => g.hd
  & tl => g.tl
| Get => toStream' (g.g s.hd) s.tl
```

# Truly "positive" coinduction-coinduction?