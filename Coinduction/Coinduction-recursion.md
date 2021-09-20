## Advanced Coinductive Types

### Coinduction-Recursion? Not really.

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

### Coinduction-Coinduction? Not really.

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

### Coinduction-Induction? Somewhat.

The classical example of a mixed coinductive-inductive type is the type of stream processors `SP A B`. It is a more concrete (even though still higher-order) representation of functions of type `Stream A -> Stream B`. The main purpose of it is to define stream processing functions which might not be accepted by the productivity checker.

```
mutual
  codata SP (A B : Type) : Type
  | Put (hd : B, tl : SP A B)
  | Get (gsp : A -> GetSP A B)

  data GetSP (A B : Type) : Type
  | Put (hd : B, tl : SP A B)
  | Get (g : A -> GetSP A B)
```

The implementation is somewhat mysterious, so let's go over it in detail.

The type `SP A B` is the type of stream processors. It is defined coinductively (using our "positive" coinductive syntax sugar), because it is supposed to represent the "output part" of a stream processing function. Since the output is a stream, and streams are coinductive, `SP A B` is also coinductive.

It has two constructors, `Put` and `Get`. `Put` should be interpreted as the function outputting a single element of the output stream (`hd : B`) and then there's the rest of the stream processors (`tl : SP A B`). `Get` is used when the function needs to see what's in the input stream before deciding on the output. Its argument `gsp` is of type `A -> GetSP A B`, which should be interpreted as "peek at the first element of the input stream and then maybe at some more, until you decide on the output".

The type `GetSP A B` is the "input part" of our stream processing. Since our stream processing function is supposed to be productive, it can only look up a finite prefix of the input stream before deciding on the output, so `GetSP A B` is an inductive type.

It has two constructors named `Put` and `Get`. `Put` should be interpreted as the function having checked enough inputs to produce an output (`hd : B`), and thus so we return to the output mode (`tl : SP A B`). `Get` should be interpreted as the function still having to see more elements of the input stream.

Ok, that's more or less it when it comes to the type itself. But since the type of stream processors was supposed to represent functions in the first place, let's see how to interpret `SP A B` as a function `Stream A -> Stream B`.

```
toStream : (f : SP A B) (s : Stream A) -> Stream B
& hd
  | Put => f.hd
  | Get => head (f.gsp s.hd) s.tl
& tl
  | Put => toStream f.tl s
  | Get => tail (f.gsp s.hd) s.tl

and
head : (g : GetSP A B) (s : Stream A) -> B
| Put => g.hd
| Get => head (g.g s.hd) s.tl

and
tail : (g : GetSP A B) (s : Stream A) -> Stream B
| Put => toStream g.tl s
| Get => tail (g.g s.hd) s.tl
```

Out first attempt consists of three mutually defined functions. The main function is `toStream`, defined corecursively, and the helper functions are `head` and `tail`, defined recursively. `toStream` works as follows. The `hd` of the result stream is extracted from the stream processor `f : SP A B` if it is a `Put` and otherwise we use the helper function `head` to compute it by feeding the input stream to `f.gsp`. As for the `tl`, we corecursively compute it from the tail of the stream processor if it is `Put` and in case it's `Get`, we use the helper function `tail` which computes it by feeding the input stream `s` to `f.gsp`.

We might be a little dissatisfied with our first attempt, however, because it looks somewhat redundant. Namely, the recursion scheme of `head` and `tail` are very similar, so maybe they could be merged?

```
toStream : (f : SP A B) (s : Stream A) -> Stream B
| Put
  & hd => f.hd
  & tl => toStream f.tl s
| Get => toStream' (f.g s.hd) s.tl

and
toStream' : (g : GetSP A B) (s : Stream A) -> Stream B
| Put
  & hd => g.hd
  & tl => toStream g.tl s
| Get => toStream' (g.g s.hd) s.tl
```

The second attempt results in a much more compact definition. `toStream` is still corecursive, but we use pattern matching at the top level to make the definition shorter. In the `Put` case, we unpack the head of the stream from the argument and compute the tail corecursively, just as in the first definition. In the `Get` case, we use `toStream'`, which computes the result stream recursively from `g : GetSP A B` and `s : Stream A`. In the `Put` case, it behaves the same as `toStream`, whereas in the `Get` case it recursively feeds the input stream `s` into `g`. As we can see, we managed to cut down the redundancy.

But we may still be somewhat dissatisfied, because `toStream` and `toStream'` are defined by mutual corecursion-recursion, which is a suspicious principle. Can we untie them so that we first define `toStream'` by recursion and only then `toStream` by corecursion? Let's try.

```
whnf : (g : GetSP A B) (s : Stream A) -> (hd : B, tl : SP A B, s : Stream A)
| Put => (g.hd, g.tl, s)
| Get => whnf (g.g s.hd) s.tl

toStream : (f : SP A B) (s : Stream A) -> Stream B
| Put
  & hd => f.hd
  & tl => toStream f.tl s
| Get =>
  let x := whnf (f.g s.hd) s.tl in
    & hd => x.hd
    & tl => toStream x.tl x.s
```

As we see, it is possible to avoid mutual corecursion-recursion. We attain this by getting rid of `toStream'` and instead defining a function called `whnf`, whose role is to feed an input stream `s` into `g : GetSP A B` in order to compute whatever is necessary for the `Get` case in `toStream`, i.e. the head of the stream, the rest of the stream processor and the remaining input stream. Our definition didn't get any shorter in the process, however. Also note that we can use `let` together with copatterns pretty seamlessly.

Papers:
- There are quite a few papers on mixing coinduction with induction, but most of them are written in the old deprecated Agda coinduction, so they aren't that much useful.

TODO:
- Currently using pattern matching means that the function is recursive, so the second definition of `toStream` is not legal. Maybe some annotation for whether a function is recursive or corecursive?
- Does `let` and copattern matching play out together as nicely as in the last example?

# Untangleable coinduction-induction?

# Untangleable coinduction-coinduction?