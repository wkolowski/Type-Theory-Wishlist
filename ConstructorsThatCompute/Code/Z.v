Require Import Recdef.

Inductive Z : Type :=
    | z : Z
    | s : Z -> Z
    | p : Z -> Z.

Function normalize (k : Z) : Z :=
match k with
    | z => z
    | s k' =>
        match normalize k' with
            | p k'' => k''
            | k'' => s k''
        end
    | p k' =>
        match normalize k' with
            | s k'' => k''
            | k'' => p k''
        end
end.

Inductive Box (A : Type) : SProp :=
    | box : A -> Box A.

Record Z' : Type :=
{
    canonical : Z;
    normalize_canonical : Box (normalize canonical = canonical);
}.

Compute normalize (s (s (s (p (p (p z)))))).
(* ===> = z : Z *)

Ltac inv H := inversion H; subst; clear H; auto.

Inductive Canonical : Z -> Prop :=
    | Canonical_z  : Canonical z
    | Canonical_sz : Canonical (s z)
    | Canonical_s  :
        forall k : Z, Canonical (s k) -> Canonical (s (s k))
    | Canonical_pz : Canonical (p z)
    | Canonical_p  :
        forall k : Z, Canonical (p k) -> Canonical (p (p k)).

Hint Constructors Canonical : core.

Lemma Canonical_normalize :
  forall k : Z,
    Canonical (normalize k).
Proof.
  intros. functional induction normalize k.
    constructor.
    rewrite e0 in IHz0. inv IHz0.
    destruct (normalize k'); auto. contradiction.
    rewrite e0 in IHz0. inv IHz0.
    destruct (normalize k'); auto. contradiction.
Qed.

Lemma normalize_Canonical :
  forall k : Z,
    Canonical k -> normalize k = k.
Proof.
  induction 1.
    cbn. reflexivity.
    cbn. reflexivity.
    rewrite normalize_equation. rewrite IHCanonical. reflexivity.
    cbn. reflexivity.
    rewrite normalize_equation. rewrite IHCanonical. reflexivity.
Qed.

Lemma normalize_idempotent :
  forall k : Z,
    normalize (normalize k) = normalize k.
Proof.
  intros.
  apply normalize_Canonical.
  apply Canonical_normalize.
Qed.

Fixpoint abs (k : Z) : Z :=
match k with
    | z => z
    | s k' => s k'
    | p k' => s (abs k')
end.

Lemma abs_abs :
  forall k : Z, abs (abs k) = abs k.
Proof.
  induction k; cbn; intros.
    reflexivity.
    reflexivity.
    reflexivity.
Qed.

Fixpoint neg (k : Z) : Z :=
match k with
    | z    => z
    | s k' => p (neg k')
    | p k' => s (neg k')
end.

Fixpoint add (k l : Z) : Z :=
match k with
    | z => l
    | s k' => s (add k' l)
    | p k' => p (add k' l)
end.

Fixpoint sub (k l : Z) : Z :=
match l with
    | z    => k
    | s l' => p (sub k l')
    | p l' => s (sub k l')
end.

Lemma sub_spec :
  forall k l : Z,
    normalize (sub k l) = normalize (add (neg l) k).
Proof.
  induction l; cbn; intros.
    reflexivity.
    rewrite IHl. reflexivity.
    rewrite IHl. reflexivity.
Qed.

Lemma abs_neg :
  forall k : Z,
    Canonical k ->
      normalize (abs (neg k)) = normalize (abs k).
Proof.
  induction k; cbn; intros.
    reflexivity.
    destruct k; cbn in *.
      reflexivity.
      rewrite IHk.
        reflexivity.
        inv H.
      inv H.
    destruct k; cbn in *.
      reflexivity.
      inv H.
      rewrite IHk.
        reflexivity.
        inv H.
Qed.

Lemma add_z_r :
  forall k : Z,
    add k z = k.
Proof.
  induction k; cbn; rewrite ?IHk; reflexivity.
Qed.

Lemma add_s_r :
  forall k l : Z,
    normalize (add k (s l)) = normalize (s (add k l)).
Proof.
  induction k; cbn; intros.
    reflexivity.
    rewrite IHk. reflexivity.
    rewrite IHk. cbn.
Admitted.

Lemma add_p_r :
  forall k l : Z,
    normalize (add k (p l)) = normalize (p (add k l)).
Proof.
  induction k; cbn; intros.
    reflexivity.
    rewrite IHk. cbn. destruct (normalize (add k l)).
Admitted.

Lemma add_comm :
  forall k l : Z,
    normalize (add k l) = normalize (add l k).
Proof.
  induction k; cbn; intros.
    rewrite add_z_r. reflexivity.
    rewrite add_s_r. cbn. rewrite IHk. reflexivity.
    rewrite add_p_r. cbn. rewrite IHk. reflexivity.
Qed.