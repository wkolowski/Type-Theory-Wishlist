Class Order : Type :=
{
    A : Type;
    le : A -> A -> Prop;
}.

Coercion A : Order >-> Sortclass.

Class LawfulOrder : Type :=
{
    Ord : Order;
    le_refl : forall x : Ord, le x x;
}.

Coercion Ord : LawfulOrder >-> Order.

Instance Dual (O : Order) : Order :=
{|
    A := A;
    le x y := le y x;
|}.

Instance Dual (R <= Order) (r : R) : R :=
{|
    A := r.A;
    le x y := r.le y x;
    
|}.

Dual LawfulOrder 