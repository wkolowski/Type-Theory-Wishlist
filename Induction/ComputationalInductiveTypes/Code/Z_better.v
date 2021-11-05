Require Import Bool Recdef StrictProp.

Inductive Z : Type :=
    | z : Z
    | s : Z -> Z
    | p : Z -> Z.

Function isNormal (k : Z) : bool :=
match k with
    | z    => true
    | s k' =>
        match k' with
            | p _ => false
            | _   => isNormal k'
        end
    | p k' =>
        match k' with
            | s _ => false
            | _   => isNormal k'
        end
end.

Record Z' : Type :=
{
    canonical : Z;
    isNormal_canonical : Squash (isNormal canonical = true);
}.

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

Ltac inv H := inversion H; subst; clear H; auto.

Inductive Canonical : Z -> Prop :=
    | Canonical_z  : Canonical z
    | Canonical_sz : Canonical (s z)
    | Canonical_s  :
        forall k : Z, Canonical (s k) -> Canonical (s (s k))
    | Canonical_pz : Canonical (p z)
    | Canonical_p  :
        forall k : Z, Canonical (p k) -> Canonical (p (p k)).

Local Hint Constructors Canonical : core.

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

Lemma Canonical_isNormal :
  forall k : Z, reflect (Canonical k) (isNormal k).
Proof.
  intro. functional induction isNormal k;
  repeat constructor.
    intro H; inv H.
    inv IHb; repeat constructor.
      inv H0; contradiction.
      intro H1; inv H1.
    intro H; inv H.
    inv IHb; repeat constructor.
      inv H0; contradiction.
      intro H1; inv H1.
Defined.

Lemma isNormal_normalize :
  forall k : Z,
    isNormal (normalize k) = true.
Proof.
  intro. functional induction normalize k; cbn.
    reflexivity.
    rewrite e0 in IHz0; cbn in *. destruct k''; congruence.
    destruct (normalize k'); cbn in *; auto.
    rewrite e0 in IHz0; cbn in *. destruct k''; congruence.
    destruct (normalize k'); cbn in *; auto.
Qed.

Lemma normalize_isNormal :
  forall k : Z,
    isNormal k = true -> normalize k = k.
Proof.
  intro. functional induction normalize k; cbn; intro Heq.
    reflexivity.
    1-4: destruct k'; cbn in *; try specialize (IHz0 Heq); congruence.
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
    isNormal k = true -> isNormal l = true -> sub k l = add (neg l) k.
Proof.
  induction l; cbn; intros.
    reflexivity.
    rewrite IHl.
      reflexivity.
      assumption.
      destruct l; congruence.
    rewrite IHl.
      reflexivity.
      assumption.
      destruct l; congruence.
Qed.

Lemma abs_neg :
  forall k : Z,
    isNormal k = true -> abs (neg k) = abs k.
Proof.
  induction k; cbn; intros.
    reflexivity.
    destruct k; cbn in *.
      reflexivity.
      rewrite (IHk H). reflexivity.
      congruence.
    destruct k; cbn in *.
      reflexivity.
      congruence.
      rewrite (IHk H). reflexivity.
Qed.

Lemma add_z_r :
  forall k : Z,
    add k z = k.
Proof.
  induction k; cbn; rewrite ?IHk; reflexivity.
Qed.

Lemma add_s_r :
  forall k l : Z,
    isNormal k = true -> isNormal l = true -> add k (s l) = s (add k l).
Proof.
  induction k; cbn; intros.
    reflexivity.
    destruct k as [| k' | k']; cbn in *.
      reflexivity.
      rewrite (IHk _ H H0). reflexivity.
      congruence.
Abort.

Compute normalize (add (s z) (p z)).
Compute normalize (p (add (s z) z)).

Lemma add_p_r :
  forall k l : Z,
    normalize (add k (p l)) = normalize (p (add k l)).
Proof.
  induction k as [| k' | k']; cbn; intros.
    reflexivity.
Admitted.

Lemma add_comm :
  forall k l : Z,
    normalize (add k l) = normalize (add l k).
Proof.
  induction k; cbn; intros.
    rewrite add_z_r. reflexivity.
    rewrite add_s_r. cbn. rewrite IHk. reflexivity. admit.
    rewrite add_p_r. cbn. rewrite IHk. reflexivity.
Admitted.