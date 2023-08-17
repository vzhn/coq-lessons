

Inductive LambdaTerm : Type :=
  | variable (n:  nat)
  | app (left: LambdaTerm) (right: LambdaTerm)
  | abst (n: nat) (b: LambdaTerm).


Fixpoint height (t: LambdaTerm) : nat :=
  match t with
    | variable n  => 1
    | app a b  => 1 + (max (height a) (height b))
    | abst _ b => 1 + (height b)
  end.

Compute (
  height 
  (app (variable 1)  (variable 2) )
).

