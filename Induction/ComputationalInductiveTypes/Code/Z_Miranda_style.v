Require Import Bool Recdef StrictProp.

Inductive Z : Type :=
    | z' : Z
    | s' : Z -> Z
    | p' : Z -> Z.

Definition z : Z := z'.

Definition s (k : Z) : Z :=
match k with
    | z'    => s' z'
    | s' k' => s' (s' k')
    | p' k' => k'
end.

Definition p (k : Z) : Z :=
match k with
    | z'    => p' z'
    | s' k' => k'
    | p' k' => p' (p' k')
end.

Function isNormal (k : Z) : bool :=
match k with
    | z'    => true
    | s' k' =>
        match k' with
            | p' _ => false
            | _    => isNormal k'
        end
    | p' k' =>
        match k' with
            | s' _ => false
            | _    => isNormal k'
        end
end.

Record Z' : Type :=
{
    canonical : Z;
    isNormal_canonical : Squash (isNormal canonical = true);
}.

Function normalize (k : Z) : Z :=
match k with
    | z' => z
    | s' k' => s (normalize k')
    | p' k' => p (normalize k')
end.

Ltac inv H := inversion H; subst; clear H; auto.

Lemma isNormal_normalize :
  forall k : Z,
    isNormal (normalize k) = true.
Proof.
  intro. functional induction normalize k; cbn.
    reflexivity.
    destruct (normalize k'); cbn in *; try destruct z0; congruence.
    destruct (normalize k'); cbn in *; try destruct z0; congruence.
Qed.

Lemma normalize_isNormal :
  forall k : Z,
    isNormal k = true -> normalize k = k.
Proof.
  intro. functional induction normalize k; cbn; intro Heq.
    reflexivity.
    rewrite IHz0; destruct k'; cbn in *; try congruence.
    rewrite IHz0; destruct k'; cbn in *; try congruence.
Qed.

Lemma normalize_idempotent :
  forall k : Z,
    normalize (normalize k) = normalize k.
Proof.
  intros. rewrite normalize_isNormal.
    reflexivity.
    apply isNormal_normalize.
Qed.

Fixpoint abs (k : Z) : Z :=
match k with
    | z'    => z
    | s' k' => s k'
    | p' k' => s (abs k')
end.

Lemma abs_abs :
  forall k : Z, abs (abs k) = abs k.
Proof.
  induction k; cbn; intros.
    reflexivity.
    unfold s. destruct k; cbn in *; try reflexivity. unfold s in *.
Abort.

Fixpoint abs' (k : Z) : Z :=
match k with
    | z'    => z'
    | s' k' => s' k'
    | p' k' => s' (abs' k')
end.

Lemma abs_abs :
  forall k : Z, abs' (abs' k) = abs' k.
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