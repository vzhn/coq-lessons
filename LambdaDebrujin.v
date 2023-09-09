 Inductive LambdaTerm :=
 | var (v: nat)
 | app (a b: LambdaTerm)
 | abst (a: LambdaTerm). 