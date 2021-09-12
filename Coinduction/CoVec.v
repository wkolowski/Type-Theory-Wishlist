Inductive NatF (X : Type) : Type :=
    | Z : NatF X
    | S : X -> NatF X.

Arguments Z {X}.
Arguments S {X} _.

CoInductive conat : Type :=
{
    out : NatF conat;
}.

Definition zero : conat :=
{|
    out := Z;
|}.

Definition succ (c : conat) : conat :=
{|
    out := S c;
|}.

CoFixpoint add (n m : conat) : conat :=
{|
    out :=
      match out n with
          | Z    => out m
          | S n' => S (add n' m)
      end
|}.

Lemma out_eq :
  forall n m : conat, out n = out m -> n = m.
Proof.
  intros [] []; cbn. intros []. reflexivity.
Qed.

Lemma add_zero_l :
  forall n : conat, add zero n = n.
Proof.
  intros. apply out_eq. cbn. reflexivity.
Qed.

Lemma add_succ_l :
  forall n m : conat, add (succ n) m = succ (add n m).
Proof.
  intros. apply out_eq. cbn. reflexivity.
Qed.

Inductive CoVecF (F : conat -> Type) (A : Type) : conat -> Type :=
    | N : CoVecF F A zero
    | C : forall (h : A) {c : conat} (t : F c), CoVecF F A (succ c).

Arguments N {F A}.
Arguments C {F A} _ {c} _.

CoInductive CoVec (A : Type) (c : conat) : Type :=
{
    out' : CoVecF (CoVec A) A c;
}.

Arguments out' {A c} _.

Definition CoNil {A : Type} : CoVec A zero :=
{|
    out' := N;
|}.

Definition CoCons {A : Type} (h : A) {c : conat} (t : CoVec A c) : CoVec A (succ c) :=
{|
    out' := C h t;
|}.

CoFixpoint vapp {A : Type} {c1 c2 : conat} (v1 : CoVec A c1) (v2 : CoVec A c2) : CoVec A (add c1 c2).
Proof.
  destruct v1 as [[]].
    rewrite add_zero_l. exact v2.
    rewrite add_succ_l. exact (CoCons h (vapp _ _ _ t v2)). Show Proof.
Defined.

CoFixpoint vapp' {A : Type} {c1 c2 : conat} (v1 : CoVec A c1) (v2 : CoVec A c2) : CoVec A (add c1 c2) :=
match out' v1 with
   | N     => eq_rect_r (CoVec A) v2                      (add_zero_l c2)
   | C h t => eq_rect_r (CoVec A) (CoCons h (vapp' t v2)) (add_succ_l _ c2)
end.