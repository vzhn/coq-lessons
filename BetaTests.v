Require Import LambdaDebrujin.
Require Import Beta.

Definition n0 := (var 0).
Definition n1 := (var 1).
Definition n2 := (var 2).
Definition n3 := (var 3).
Definition n4 := (var 4).
Definition n5 := (var 5).
Definition n6 := (var 6).

Example beta_example_007: 
 beta (app (abst n3) n6) = n2.
Proof. simpl. reflexivity. Qed.

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