data IList (A : Type) : Nat -> Type
| Nil  : List 0
| Cons : (hd : A, #n : Nat, tl : IList n) -> IList (s n)

codata IStream (A : Type) : CoNat -> Type
& hd : (#c : Conat) -> IStream c -> A
& tl : (#c : Conat) -> IStream c -> IStream (pred c)

// Better - no need to explicitly quantify `c`.

codata IStream (A : Type) : CoNat -> Type
& hd : IStream c -> A
& tl : IStream c -> IStream (pred c)

// "Possibly finite" IStreams...
codata IStream (A : Type) : CoNat -> Type
& hd : IStream (succ c) -> A
& tl : IStream (succ c) -> IStream c


```
codata Linked (R : A -> A -> Prop) : (s : Stream A) -> Prop
& link  : Linked s -> R s.hd s.tl.hd
& links : Linked s -> Linked s.tl
```

```
codata Even : CoNat -> Prop
| Ez : Even z
| Es : (#n : CoNat) -> Odd n -> Even (s n)

and

codata Odd : CoNat -> Prop
| Os : (#n : CoNat) -> Even n -> Odd (s n)
```

```
codata Odd : CoNat -> Prop
& Oz : Odd z -> Empty
& Os : (#n : CoNat) -> Odd (s n) -> Even n

and

codata Even : CoNat -> Prop
& Osz : Even (s z) -> Empty
& Es  : (#n : CoNat) -> Even (s n) -> Odd n

```

```
// HITs?
codata CoDense (R : A -> A -> Prop) : Type
| in   (x : A)
| mid #(x y : CoDense) (H : CoDense-R R x y)
| eq  #(x   : CoDense) (H : CoDense-R R x x) with (i : I)
  //| i0 => mid x x H
  //| i1 => in x

and

codata CoDense-R (R : A -> A -> Prop) : CoDense R -> CoDense R -> Prop
| in   : #(x y : A) (H : R x y) -> CoDense-R (in x) (in y)
| midl : #(x y : CoDense R) (H : CoDense-R x y) -> CoDense-R (mid x y H) y
| midr : #(x y : CoDense R) (H : CoDense-R x y) -> CoDense-R x (mid x y H)
```