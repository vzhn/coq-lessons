Require Import Coq.Init.Nat.

Inductive LambdaTerm :=
| var (v: nat)
| app (a b: LambdaTerm)
| abst (a: LambdaTerm). 

Fixpoint lambda_eq (a b: LambdaTerm): bool :=
match a, b with
| var v1, var v2 => v1 =? v2
| app a1 b1, app a2 b2 => lambda_eq a1 a2 && lambda_eq b1 b2
| abst a1, abst a2 => lambda_eq a1 a2
| _, _ => false
end.