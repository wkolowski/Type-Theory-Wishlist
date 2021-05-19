Inductive Z' : Set :=
  | z' : Z'
  | s' : Z' -> Z'
  | p' : Z' -> Z'.

Fixpoint canon (k' : Z') : Z' :=
match k' with
    | s' (p' l') => canon l'
    | p' (s' l') => canon l'
    | _ => k'
end.

Inductive Box (A : Type) : SProp :=
    | box : A -> Box A.

Record Subtype {A : Type} (P : A -> SProp) : Type :=
{
    elem : A;
    spec : P elem;
}.

Record Z : Type :=
{
    k' : Z';
    k'_canon : canon k' = k';
}.

