Require Import LambdaDebrujin.

Fixpoint _mk_app (n: nat) :=
 match n with
  | O => var 0
  | S n => app (var 1) (_mk_app n)
 end.

Definition nat_to_church (n: nat): LambdaTerm :=
  abst (abst (_mk_app n)).

Fixpoint _app_to_nat (t: LambdaTerm): (option nat) :=
  match t with
    | var 0 => Some 0
    | app (var 1) a => match (_app_to_nat a) with
                       | Some k => Some (S k)
                       | _ => None
                       end
    | _ => None
  end.

Definition succ := 
  (abst (abst (abst (app (var 1) (app (app (var 2) (var 1)) (var 0)))))).

Definition church_to_nat (ch: LambdaTerm): (option nat) :=
  match ch with
    | (abst (abst a)) => _app_to_nat a
    | _ => None
  end.