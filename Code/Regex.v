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