Require Import List.
Import ListNotations.

Inductive ElemF {A : Type} (E : list A -> Type) (x h : A) (t : list A) : list A -> Type :=
    | ElemF_Z :
        ElemF E x h t (x :: t)
    | ElemF_S :
        forall e : E t, ElemF E x h t (h :: t).

Unset Guard Checking.
Fixpoint Elem {A : Type} (x : A) (l : list A) {struct l} : Type :=
match l with
    | []     => False
    | h :: t => ElemF (Elem x) x h t (h :: t)
end.
Set Guard Checking.

Goal Elem 2 [1; 22; 3; 4; 5; 2].
Proof.
  cbn. right. cbn. right. cbn. right.
  cbn. right. cbn. right. cbn. left.
Restart.
  do 5 right. right. cbn. left.
Qed.