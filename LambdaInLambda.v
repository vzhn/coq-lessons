Require Import LambdaDebrujin.
Require Import Church.
Require Import Beta.

Fixpoint encode_lambda (t: LambdaTerm) := 
let zero := nat_to_church 0 in
let one := nat_to_church 1 in
let two := nat_to_church 2 in
match t with
| var n => app (app church_pair zero) (nat_to_church n)
| app a b => app (app church_pair one) 
                 (app (app church_pair (encode_lambda a)) 
                      (app church_pair (encode_lambda b)))
| abst body => app (app church_pair two) (encode_lambda body)
end.

