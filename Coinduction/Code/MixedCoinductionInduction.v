Require Import F3. (* Streams. *)

Inductive SPXY (X Y A B : Type) : Type :=
    | PutX : B -> SPXY X Y A B -> SPXY X Y A B
    | GetX : (A -> Y) -> SPXY X Y A B.

Inductive GetSPX (X A B : Type) : Type :=
    | GPutX : B -> SPXY X (GetSPX X A B) A B -> GetSPX X A B
    | GGetX : (A -> GetSPX X A B) -> GetSPX X A B.

Arguments PutX {X Y A B} _ _.
Arguments GetX {X Y A B} _.

Arguments GPutX {X A B} _ _.
Arguments GGetX {X A B} _.

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
    | GPutX h t => h
    | GGetX g'  => head (g' (hd s)) (tl s)
end.

Fixpoint tail {A B : Type} (g : GetSP A B) (s : Stream A) : SP A B * Stream A :=
match g with
    | GPutX h t => ({| Out := t |}, s)
    | GGetX g'  => tail (g' (hd s)) (tl s)
end.

CoFixpoint toStream {A B : Type} (f : SP A B) (s : Stream A) : Stream B :=
{|
    hd :=
      match Out f with
          | PutX h t => h
          | GetX g   => head (g (hd s)) (tl s)
      end;
    tl :=
      match Out f with
          | PutX h t => toStream {| Out := t |} s
          | GetX g   => let (f', s') := tail (g (hd s)) (tl s) in toStream f' s'
      end;
|}.

(** A better way. *)

Fixpoint aux {A B : Type} (g : GetSP A B) (s : Stream A) : B * SP A B * Stream A :=
match g with
    | GPutX h t => (h, {| Out := t |}, s)
    | GGetX g'  => aux (g' (hd s)) (tl s)
end.

CoFixpoint toStream' {A B : Type} (f : SP A B) (s : Stream A) : Stream B :=
match Out f with
    | PutX h t =>
        {|
            hd := h;
            tl := toStream' {| Out := t |} s;
        |}
    | GetX g   => let '(h, f', s') := aux (g (hd s)) (tl s) in
        {|
            hd := h;
            tl := toStream f' s';
        |}
end.