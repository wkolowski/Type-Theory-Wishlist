Partial types - something like Singleton Types, but we use definitional equality instead of boolean predicates. Examples:
1. {x : nat ^^^ x = S (S ?n)} - type of naturals that definitionally compute to `2 + something`. How do we compute with this? Dunno, but maybe `coe : {x : nat ^^^ _} -> nat`, with the rule `coe x => S (S ?n)`, whatever that means.
2. {l : list A ^^^ l = []} - singleton type of empty lists.
3. {p : nat * nat ^^^ fst p = 42} - type of pairs of naturals whose left component is definitionally equal to `42`, i.e. `fst (coe p) = 42`.
4. {x : nat + bool ^^^ x = inr ?b} - sum type of `nat` and `bool`, but its element are definitionally equal to `inr something`, so that `match coe x with | inl a => f a | inr b => g b end` computes to `g ?b`.
5. {s : Stream nat ^^^ hd s = 42} - type of streams whose head is `42`.
6. {f : bool -> nat ^^^ f true = 42} - type of functions from `bool` to nat` that compute to `42` on `true`.
7. {f : bool -> nat ^^^ f true = f false} - type of definitionally weakly constant functions from `bool` to `nat`.
8. {f : bool -> nat ^^^ f _ = 42} - type of definitionally strongly constant functions that always returns `42`.
9. Maybe we need intersection and union types for this?
10. {r : {fst : nat; snd : bool; trd : list nat} ^^^ r.fst = 42 & r.snd = false} - type of records with three fields, two of which are definitionally set.