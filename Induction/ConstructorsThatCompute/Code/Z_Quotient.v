Inductive Z : Type :=
    | pair : nat -> nat -> Z.

Require Import Recdef.

Function normalize (n m : nat) : nat * nat :=
match n, m with
    | S n', S m' => normalize n' m'
    | _   , _    => (n, m)
end.

Definition normalize' (k : Z) : Z :=
match k with
    | pair n m => let (n', m') := normalize n m in pair n' m'
end.

Inductive Box (A : Type) : SProp :=
    | box : A -> Box A.

Record Z' : Type :=
{
    num : Z;
    normalize_num : Box (normalize' num = num);
}.

Lemma normalize_idempotent :
  forall n m n' m' : nat,
    normalize n m = (n', m') ->
      normalize n' m' = (n', m').
Proof.
  intros.
  functional induction normalize n m.
    apply IHp. assumption.
    destruct n, m; inversion H; subst; cbn.
      1-3: reflexivity.
      contradiction.
Qed.

Lemma normalize'_idempotent :
  forall k : Z,
    normalize' (normalize' k) = normalize' k.
Proof.
  intros [n m].
  unfold normalize'.
  destruct (normalize n m) eqn: Heq1.
  destruct (normalize n0 n1) eqn: Heq2.
  erewrite normalize_idempotent in Heq2.
    congruence.
    eassumption.
Qed.