Require Import Coq.Init.Nat.

Inductive LambdaTerm :=
| var (v: nat)
| app (a b: LambdaTerm)
| abst (a: LambdaTerm).

Definition s_comb := (abst (abst (abst 
  (app (app (var 2) (var 0)) (app (var 1) (var 0)))))).

Definition k_comb := (abst (abst (var 1))).

(* 
  beta-reduction (λ M) N 
  1. find bound instances
  2. decrement free variables of M
  3. replace bound instances with N, incrementing free variables of N

  example
   ((abst (abst (app (app (var 3) (var 1)) (abst (app (var 0) (var 2)))))) (abst (app (var 4) (var 0)))) -> 

   (abst (app (app (var 2) (abst (app (var 5) (var 0)))) (abst (app (var 0) (abst (app (var 6) (var 0)))))))
*)

Fixpoint dec_free_vars (t: LambdaTerm) (depth: nat): LambdaTerm :=
match t with  
| var 0 => t
| var (S n) => if (depth <=? n)
               then var n
               else t
| app a b => app (dec_free_vars a depth) (dec_free_vars b depth)
| abst a => abst (dec_free_vars a (S depth))
end.

Fixpoint inc_free_vars (t: LambdaTerm) (depth: nat): LambdaTerm :=
match t with
| var n => if (depth <=? n)
            then var (S n)
            else t
| app a b => app (inc_free_vars a depth) (inc_free_vars b depth)
| abst a => abst (inc_free_vars a (S depth))
end.

Theorem inv_fv:
 forall (t: LambdaTerm) (depth: nat),
 (dec_free_vars (inc_free_vars t depth) depth) = t.
Proof.
Admitted.

Example dec_example_001: dec_free_vars (var 0) 0 = (var 0).
Proof. simpl. reflexivity. Qed.

Example inc_example_001: inc_free_vars (var 0) 0 = (var 1).
Proof. simpl. reflexivity. Qed.

Example dec_example_002: dec_free_vars (var 1) 0 = (var 0).
Proof. simpl. reflexivity. Qed.

Example inc_example_002: inc_free_vars (var 0) 0 = (var 1).
Proof. simpl. reflexivity. Qed.

Example dec_example_003: dec_free_vars (var 2) 0 = (var 1).
Proof. simpl. reflexivity. Qed.

Example inc_example_003: inc_free_vars (var 1) 0 = (var 2).
Proof. simpl. reflexivity. Qed.

Example dec_example_004: dec_free_vars (var 3) 0 = (var 2).
Proof. simpl. reflexivity. Qed.

Example dec_example_005: dec_free_vars (var 4) 0 = (var 3).
Proof. simpl. reflexivity. Qed.

Example dec_example_006: dec_free_vars (var 0) 1 = (var 0).
Proof. simpl. reflexivity. Qed.

Example dec_example_007: dec_free_vars (var 1) 1 = (var 1).
Proof. simpl. reflexivity. Qed.

Example dec_example_008: dec_free_vars (var 2) 1 = (var 1).
Proof. simpl. reflexivity. Qed.

Example dec_example_009: dec_free_vars (var 3) 1 = (var 2).
Proof. simpl. reflexivity. Qed.



