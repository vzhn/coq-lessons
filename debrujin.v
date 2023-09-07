Require Import Coq.Init.Nat.

Inductive LambdaTerm :=
| var (v: nat)
| app (a b: LambdaTerm)
| abst (a: LambdaTerm).

Definition n0 := (var 0).
Definition n1 := (var 1).
Definition n2 := (var 2).
Definition n3 := (var 3).
Definition n4 := (var 4).
Definition n5 := (var 5).
Definition n6 := (var 6).

Fixpoint lambda_eq (a b: LambdaTerm): bool :=
match a, b with
| var v1, var v2 => v1 =? v2
| app a1 b1, app a2 b2 => lambda_eq a1 a2 && lambda_eq b1 b2
| abst a1, abst a2 => lambda_eq a1 a2
| _, _ => false
end.

Definition s_comb := (abst (abst (abst (app (app (var 2) (var 0)) (app (var 1) (var 0)))))).

Definition k_comb := (abst (abst (var 1))).

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

(*
  From Wiki:
  beta-reduction (\u03bb M) N 
  1. find bound instances in M
  2. decrement free variables of M
  3. replace bound instances of M with N, incrementing free variables of N

  example
   ((abst (abst (app (app (var 3) (var 1)) (abst (app (var 0) (var 2)))))) (abst (app (var 4) (var 0)))) -> 

   (abst (app (app (var 2) (abst (app (var 5) (var 0)))) (abst (app (var 0) (abst (app (var 6) (var 0)))))))
*)

Fixpoint beta (t: LambdaTerm): LambdaTerm :=
match t with
| (app (abst a) b) => (dec_free_vars (replace_instances a b 0) 0)
| app a b => let ba := beta a in
               if (lambda_eq a ba)
                then app a (beta b)
                else app ba b
| _ => t
end.

Example beta_example_007: 
 beta (app (abst n3) n6) = n2.
Proof. simpl. reflexivity. Qed.


Theorem inv_fv_simple_v1:
 forall (t: LambdaTerm) (depth: nat),
 (dec_free_vars (inc_free_vars (var 0) depth 1) depth) = (var 0).
Proof.
 induction depth.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Example inc_000: inc_free_vars (var 0) 0 1 = var 1.
Proof. simpl. reflexivity. Qed.

Example inc_001: inc_free_vars (var 0) 1 1 = var 0.
Proof. simpl. reflexivity. Qed.

Example inc_002: inc_free_vars (var 1) 1 1 = var 2.
Proof. simpl. reflexivity. Qed.

Example inc_003: inc_free_vars (abst (var 0)) 0 1 = (abst (var 0)).
Proof. simpl. reflexivity. Qed.

Example inc_004: inc_free_vars (abst (var 1)) 0 1 = (abst (var 2)).
Proof. simpl. reflexivity. Qed.

Example inc_005: inc_free_vars (abst (abst (var 2))) 0 1 = (abst (abst (var 3))).
Proof. simpl. reflexivity. Qed.

Example inc_006: inc_free_vars (abst (abst (var 3))) 0 1 = (abst (abst (var 4))).
Proof. simpl. reflexivity. Qed.

Example inc_007: inc_free_vars (abst (abst (var 1))) 0 1 = (abst (abst (var 1))).
Proof. simpl. reflexivity. Qed.

Example inc_008: inc_free_vars (abst (abst (var 2))) 1 1 = (abst (abst (var 2))).
Proof. simpl. reflexivity. Qed.

Example inc_009: inc_free_vars (abst (abst (var 2))) 0 1 = (abst (abst (var 3))).
Proof. simpl. reflexivity. Qed.

Example beta_example_001: beta (app (abst (var 0)) (app (var 0) (var 1))) = (app (var 0) (var 1)).
Proof. simpl. reflexivity. Qed.

Example beta_example_006: 
 beta (app (abst (abst (app (var 0) (var 1)))) (var 0)) = 
      (abst (app (var 0) (var 1))).
Proof. simpl. reflexivity. Qed.


Example beta_example_002:
 beta (app (abst (abst (abst (abst (var 3))))) (abst (app (var 0) (var 1)))) =
 (abst (abst (abst (abst (app (var 0) (var 4)))))).
Proof. simpl. reflexivity. Qed.


Example beta_example_005: 
 beta (app (abst (abst n3)) n6) = abst n2.
Proof. simpl. reflexivity. Qed.



Example beta_example_004: 
 beta (app (abst (abst (app n3 n1))) n3) = 
 abst (app n2 n4).
Proof. simpl. reflexivity. Qed.

Example beta_example_008: 
 beta (app (abst (abst n3)) n6) = 
 abst n2.
Proof. simpl. reflexivity. Qed.

Example beta_example_009: 
 beta (app (abst (abst (app (app n3 n1) (abst (app n0 n2)))))
           n3) = 
 abst (app (app n2 n4) 
           (abst (app n0 n5))).
Proof. simpl. reflexivity. Qed.

Example beta_example_003: 
 beta (app (abst (abst (app (app n3 n1) (abst (app n0 n2)))))
           (abst (app n4 n0))) = 
 abst (app (app n2 (abst (app n5 n0))) 
           (abst (app n0 (abst (app n6 n0))))).
Proof. simpl. reflexivity. Qed.


