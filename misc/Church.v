Require Import LambdaDebrujin.

Fixpoint _mk_app (n: nat) :=
 match n with
  | O => var 0
  | S n => app (var 1) (_mk_app n)
 end.

Fixpoint _app_to_nat (t: LambdaTerm): (option nat) :=
  match t with
    | var 0 => Some 0
    | app (var 1) a => match (_app_to_nat a) with
                       | Some k => Some (S k)
                       | _ => None
                       end
    | _ => None
  end.

Definition church_succ := 
  (abst (abst (abst (app (var 1) (app (app (var 2) (var 1)) (var 0)))))).

Definition church_true := (abst (abst (var 1))).
Definition church_false := (abst (abst (var 0))).
Definition church_and := (abst (abst (app (app (var 1) (var 0)) (var 1)))).
Definition church_or := (abst (abst (app (app (var 1) (var 1)) (var 0)))).
Definition church_not := (abst (abst (abst (app (app (var 2) (var 0)) (var 1))))).
Definition church_xor := (abst (abst (app (app (var 1) (app church_not (var 0))) (var 0)))).
Definition church_if := (abst (abst (abst (app (app (var 2) (var 1)) (var 0))))).
Definition church_pair := (abst (abst (abst (app (app (var 0) (var 2)) (var 1))))).
Definition church_first := (abst (app (var 0) (abst (abst (var 1))))).
Definition church_second := (abst (app (var 0) (abst (abst (var 0))))).
Definition church_is_zero := (abst (app (app (var 0) (abst church_false)) church_true)).
Definition bool_to_church (b: bool): LambdaTerm :=
match b with
| true => church_true
| false => church_false
end.

Definition church_to_bool (ch: LambdaTerm): bool := lambda_eq ch church_true.

Definition nat_to_church (n: nat): LambdaTerm :=
  abst (abst (_mk_app n)).

Definition church_to_nat (ch: LambdaTerm): (option nat) :=
  match ch with
    | (abst (abst a)) => _app_to_nat a
    | _ => None
  end.
