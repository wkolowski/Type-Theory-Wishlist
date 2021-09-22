Require Import F3. (* Streams. *)

Inductive SPXY (X Y A B : Type) : Type :=
    | PutX : B -> X -> SPXY X Y A B
    | GetX : (A -> Y) -> SPXY X Y A B.

Arguments PutX {X Y A B} _ _.
Arguments GetX {X Y A B} _.

Inductive GetSPX (X A B : Type) : Type :=
    | In : SPXY X (GetSPX X A B) A B -> GetSPX X A B.

Arguments In {X A B} _.

CoInductive SP (A B : Type) : Type :=
{
    Out : SPXY (SP A B) (GetSPX (SP A B) A B) A B;
}.

Arguments Out {A B} _.

Definition GetSP (A B : Type) : Type :=
  GetSPX (SP A B) A B.

(** The first, naive way of doing it. *)

Fixpoint head {A B : Type} (g : GetSP A B) (s : Stream A) : B :=
match g with
    | In (PutX h t) => h
    | In (GetX g')  => head (g' (hd s)) (tl s)
end.

Fixpoint tail {A B : Type} (g : GetSP A B) (s : Stream A) : SP A B * Stream A :=
match g with
    | In (PutX h t) => (t, s)
    | In (GetX g')  => tail (g' (hd s)) (tl s)
end.

CoFixpoint toStream {A B : Type} (f : SP A B) (s : Stream A) : Stream B :=
{|
    hd :=
      match Out f with
          | PutX h _ => h
          | GetX g   => head (g (hd s)) (tl s)
      end;
    tl :=
      match Out f with
          | PutX _ t => toStream t s
          | GetX g   => let (f', s') := tail (g (hd s)) (tl s) in toStream f' s'
      end;
|}.

(** A better way. *)

Fixpoint aux {A B : Type} (g : GetSP A B) (s : Stream A) : B * (SP A B * Stream A) :=
match g with
    | In (PutX h t) => (h, (t, s))
    | In (GetX g')  => aux (g' (hd s)) (tl s)
end.

CoFixpoint toStream' {A B : Type} (f : SP A B) (s : Stream A) : Stream B :=
match Out f with
    | PutX h t =>
        {|
            hd := h;
            tl := toStream' t s;
        |}
    | GetX g   => let '(h, (f', s')) := aux (g (hd s)) (tl s) in
        {|
            hd := h;
            tl := toStream' f' s';
        |}
end.

(** Lighter syntax. *)

CoFixpoint toStream'' {A B : Type} (f : SP A B) (s : Stream A) : Stream B :=
match Out f with
    | PutX h t => scons h (toStream'' t s)
    | GetX g   =>
        let '(h, (f', s')) := aux (g (hd s)) (tl s) in
          scons h (toStream'' f' s')
end.

(** Some proofs. *)

Lemma head_aux :
  forall {A B : Type} (g : GetSP A B) (s : Stream A),
    head g s = fst (aux g s).
Proof.
  fix IH 3.
  intros A B [[h t | g']] s; cbn.
    reflexivity.
    apply IH.
Qed.

Lemma tail_aux :
  forall {A B : Type} (g : GetSP A B) (s : Stream A),
    tail g s = snd (aux g s).
Proof.
  fix IH 3.
  intros A B [[h t | g']] s; cbn.
    reflexivity.
    apply IH.
Qed.

Lemma eq_Out :
  forall {A B : Type} (x y : SP A B),
    Out x = Out y -> x = y.
Proof.
  intros A B [] []. cbn. destruct 1. reflexivity.
Qed.

Lemma eq_Stream :
  forall {A : Type} (s1 s2 : Stream A),
    hd s1 = hd s2 -> tl s1 = tl s2 -> s1 = s2.
Proof.
  intros A [] []. cbn. intros [] []. reflexivity.
Qed.

Lemma toStream'_eq :
  forall {A B : Type} (f : SP A B) (s : Stream A),
    toStream' f s =
    match Out f with
        | PutX h t =>
            {|
                hd := h;
                tl := toStream' t s;
            |}
        | GetX g   => let '(h, (f', s')) := aux (g (hd s)) (tl s) in
            {|
                hd := h;
                tl := toStream' f' s';
            |}
    end.
Proof.
  intros. apply eq_Stream. destruct f as [[]]; cbn.
Admitted.

Lemma toStream_toStream' :
  forall {A B : Type} (f : SP A B) (s : Stream A),
    sim (toStream f s) (toStream' f s).
Proof.
  cofix CH.
  destruct f as [[h t | gsp]].
    constructor; cbn.
      reflexivity.
      apply CH.
    {
      constructor; cbn.
        rewrite head_aux, toStream'_eq. cbn. destruct (aux (gsp (hd s)) (tl s)), p; cbn. reflexivity.
        rewrite tail_aux, toStream'_eq. cbn. destruct (aux (gsp (hd s)) (tl s)), p; cbn. apply CH.
    }
Qed.