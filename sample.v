Require Import Coq.Init.Nat.

Inductive LambdaTerm : Type :=
  | variable (n:  nat)
  | app (left: LambdaTerm) (right: LambdaTerm)
  | abst (n: nat) (b: LambdaTerm).


Fixpoint height (t: LambdaTerm) : nat :=
  match t with
    | variable n => 1
    | app a b  => 1 + (max (height a) (height b))
    | abst _ b => 1 + (height b)
  end.

Fixpoint substitution (t: LambdaTerm) (n: nat) (replacement: LambdaTerm): LambdaTerm := 
  match t with
    | variable v => if (v =? n) then replacement else t
    | app a b => app (substitution a n replacement) (substitution b n replacement)
    | abst v b => if (v =? n) then t else abst v (substitution b n replacement)
  end.


Fixpoint has_redex (t: LambdaTerm): bool :=
  match t with
    | variable v => false
    | app a b => (match a with
                   | abst _ _ => true
                   | _ => has_redex a
                 end) || (has_redex b)
    | abst v b => has_redex b
  end.

Fixpoint beta (t: LambdaTerm): LambdaTerm :=
  match t with
    | variable v => t
    | app a b => match a with 
                   | abst n body => substitution body n b
                   | _ => app a (beta b)
                 end
    | abst v b => abst v (beta b)
  end.


Compute (
  height 
  (app (variable 1)  (variable 2) )
).

