Require Import LambdaDebrujin.
Require Import Beta.
Require Import Church.

Example succ_test_0:
 (beta_fuel (app church_succ (nat_to_church 0))) = (nat_to_church 1).
Proof. simpl. reflexivity. Qed.

Example succ_test_1:
 (beta_fuel (app church_succ (nat_to_church 1))) = (nat_to_church 2).
Proof. simpl. reflexivity. Qed.

Example succ_test_2:
 (beta_fuel (app church_succ (nat_to_church 2))) = (nat_to_church 3).
Proof. simpl. reflexivity. Qed.

Example and_check:
 forall a b: bool, (beta_fuel (app (app church_and (bool_to_church a)) (bool_to_church b))) = bool_to_church (andb a b).
Proof. 
 destruct a, b.
 - simpl. reflexivity. 
 - simpl. reflexivity. 
 - simpl. reflexivity. 
 - simpl. reflexivity. 
Qed.

Example or_check:
 forall a b: bool, (beta_fuel (app (app church_or (bool_to_church a)) (bool_to_church b))) = bool_to_church (orb a b).
Proof. 
 destruct a, b.
 - simpl. reflexivity. 
 - simpl. reflexivity. 
 - simpl. reflexivity. 
 - simpl. reflexivity. 
Qed.

Example xor_check:
 forall a b: bool, (beta_fuel (app (app church_xor (bool_to_church a)) (bool_to_church b))) = bool_to_church (xorb a b).
Proof. 
 destruct a, b.
 - simpl. reflexivity.
 - simpl. reflexivity.
 - simpl. reflexivity.
 - simpl. reflexivity.
Qed.

Example not_check:
 forall a: bool, beta_fuel (app church_not (bool_to_church a)) = bool_to_church (negb a).
Proof. 
 destruct a.
 - simpl. reflexivity.
 - simpl. reflexivity.
Qed.

Example test_if_true:
 beta_fuel (app (app (app church_if church_true) (nat_to_church 42)) (nat_to_church 17)) = (nat_to_church 42).
Proof. simpl. reflexivity. Qed.

Example test_if_false:
 beta_fuel (app (app (app church_if church_false) (nat_to_church 42)) (nat_to_church 17)) = (nat_to_church 17).
Proof. simpl. reflexivity. Qed.

Example test_if_zero:
 beta_fuel (app church_is_zero (nat_to_church 0)) = church_true.
Proof. simpl. reflexivity. Qed.

Example test_pair_first: 
 beta_fuel (app church_first (app (app church_pair (nat_to_church 2)) (nat_to_church 3))) = nat_to_church 2.
Proof. simpl. reflexivity. Qed.

Example test_pair_second: 
 beta_fuel (app church_second (app (app church_pair (nat_to_church 2)) (nat_to_church 3))) = nat_to_church 3.
Proof. simpl. reflexivity. Qed.
