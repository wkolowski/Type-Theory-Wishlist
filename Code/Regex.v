Set Implicit Arguments.
Set Maximal Implicit Insertion.

Require Import Bool.
Require Import List.
Import ListNotations.

Require Import Equality.

Inductive Regex (A : Type) : Type :=
    | Empty
    | Epsilon
    | Char    (c : A)
    | Seq     (r1 r2 : Regex A)
    | Or      (r1 r2 : Regex A)
    | Star    (r : Regex A).

Arguments Empty {A}.
Arguments Epsilon {A}.

Require Import Recdef.

Fixpoint containsEpsilon
  {A : Type} (r : Regex A) : bool :=
match r with
    | Empty => false
    | Epsilon => true
    | Char _ => false
    | Seq r1 r2 => containsEpsilon r1 && containsEpsilon r2
    | Or r1 r2 => containsEpsilon r1 || containsEpsilon r2
    | Star _ => true
end.

Function normalize {A : Type} (r : Regex A) : Regex A :=
match r with
    | Empty => Empty
    | Epsilon => Epsilon
    | Char x => Char x
    | Seq r1 r2 =>
        match normalize r1, normalize r2 with
            | Empty, _ => Empty
            | _, Empty => Empty
            | Epsilon, r2' => r2'
            | r1', Epsilon => r1'
            | (Seq r11 r12), r2 => Seq r11 (Seq r12 r2)
            | (Or r11 r12), r2 => Or (Seq r11 r2) (Seq r12 r2)
            | r1', r2' => Seq r1' r2'
        end
    | Or r1 r2 =>
        match normalize r1, normalize r2 with
            | Empty, r2' => r2'
            | r1', Empty => r1'
(*             | Epsilon, r2' => if containsEpsilon r2' then r2' else Or Epsilon r2' *)
(*             | r1', Epsilon => if containsEpsilon r1' then r1' else Or r1' Epsilon *)
            | (Or r11 r12), r2 => Or r11 (Or r12 r2)
            | r1', r2' => Or r1' r2'
        end
    | Star r' =>
        match normalize r' with
            | Empty => Epsilon
            | Epsilon => Epsilon
            | Star r'' => Star r''
            | r'' => Star r''
        end
end.

Lemma normalize_idempotent :
  forall {A : Type} (r : Regex A),
    normalize (normalize r) = normalize r.
Proof.
  intros.
  functional induction normalize r;
  try reflexivity; try assumption.
    rewrite e0 in *. cbn in *.
      destruct (normalize r11), (normalize r12); rewrite ?IHr1; try congruence.
        destruct (normalize r2); try congruence; try contradiction.
        destruct (normalize r2); try congruence; try contradiction.
        destruct (normalize r2); try congruence; try contradiction.
Abort.

(*
Record MEpsilon {A : Type} (l : list A) : Type :=
{
    mepsilon : l = [];
}.

Record MChar {A : Type} (l : list A) (c : A) : Type :=
{
    mchar : l = [c];
}.

Record MSeq
  {A : Type}
  (l : list A) (r1 r2 : Regex A) (M : list A -> Regex A -> Type)
  : Type :=
{
    mseq_l1 : list A;
    mseq_l2 : list A;
    mseq_p  : l = mseq_l1 ++ mseq_l2;
    mseq_m1 : M mseq_l1 r1;
    mseq_m2 : M mseq_l2 r2;
}.

Fixpoint Matches {A : Type} (l : list A) (r : Regex A) {struct r} : Type :=
match r with
    | Empty     => False
    | Epsilon   => MEpsilon l
    | Char c    => MChar l c
    | Or r1 r2  => Matches l r1 + Matches l r2
    | Seq r1 r2 => MSeq l r1 r2 Matches
    | Star r'   => False (*MStar (ms : MatchesStar l r)*)
end.
*)