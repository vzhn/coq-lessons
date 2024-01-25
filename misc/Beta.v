Require Import Coq.Init.Nat.
Require Import LambdaDebrujin.

Fixpoint dec_free_vars (t: LambdaTerm) (depth: nat): LambdaTerm :=
match t with  
| var 0 => t
| var (S n) => if (depth <=? n) 
               then var n
               else t
| app a b => app (dec_free_vars a depth) (dec_free_vars b depth)
| abst a => abst (dec_free_vars a (S depth))
end.

(* depth = 0 -> 'every variable is free' *)
(* depth = 1 -> 'every variable except 0 is free' *)
(* depth = 2 -> 'every variable except 0, 1 is free' *)
(* depth = n -> 'every variable < n is free' *)
Fixpoint inc_free_vars (t: LambdaTerm) (depth: nat) (amount: nat): LambdaTerm :=
match t with
| var n => if (depth <=? n)
            then var (n + amount)
            else t
| app a b => app (inc_free_vars a depth amount) (inc_free_vars b depth amount)
| abst a => abst (inc_free_vars a (S depth) amount)
end.

(* starting from depth = 0 *)
Fixpoint replace_instances (a b: LambdaTerm) (depth: nat) :=
match a with
| var v => if (v =? depth) 
           then (inc_free_vars b 0 (1 + depth))
           else var v
| app l r => app (replace_instances l b depth) (replace_instances r b depth)
| abst body => abst (replace_instances body b (S depth))
end.

Fixpoint beta (t: LambdaTerm): LambdaTerm :=
match t with
| (app (abst a) b) => (dec_free_vars (replace_instances a b 0) 0)
| app a b => let ba := beta a in
               if (lambda_eq a ba)
                then app a (beta b)
                else app ba b
| abst body => abst (beta body)
| _ => t
end.

Definition RBeta (a b: LambdaTerm): Prop := (beta a) = b.

Fixpoint _beta_fuel (t: LambdaTerm) (fuel: nat): LambdaTerm :=
  match fuel with
  | 0 => t
  | S n => let bt := beta t in
             if (lambda_eq t bt)
               then t
               else _beta_fuel bt n
  end.

Definition beta_fuel (t: LambdaTerm): LambdaTerm :=
  _beta_fuel t 100.

Definition betan (t: LambdaTerm): LambdaTerm :=
  beta (beta t).

Definition beta3 (t: LambdaTerm): LambdaTerm :=
  beta (beta (beta t)).

Definition beta4 (t: LambdaTerm): LambdaTerm :=
  beta (beta (beta (beta t))).
