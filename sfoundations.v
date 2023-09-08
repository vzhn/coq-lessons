Require Import Coq.Init.Nat.

Theorem plus_id_example: 
 forall n m: nat, n = m -> n + n = m + m.
Proof.
 intros n m.
 intros H.
 rewrite -> H.
 reflexivity.
Qed.

Theorem plus_id_excercise : forall n m o: nat,
 n = m -> m = o -> n + m = m + o.
Proof.
 intros m n o.
 intros HA.
 intros HB.
 rewrite -> HA.
 rewrite -> HB.
 reflexivity.
Qed.

Theorem mult_n_0: forall n, n * 0 = 0.
Proof.
 intros.
 auto.
Qed.

Theorem mult_n_0_m_0:
 forall p q: nat,
 (p * 0) + (q * 0) = 0.
Proof.
 intros p q.
 rewrite <- mult_n_O.
 rewrite <- mult_n_O.
 reflexivity.
Qed.

Theorem plus_1_neq_0_firsttry: forall n: nat,
 (n + 1) =? 0 = false.
Proof.
 intros n.
 simpl.
Abort.

Theorem plus_1_neq_0 : forall n : nat,
 (n + 1) =? 0 = false.
Proof.
 intros n.
 destruct n as [| n'] eqn: E.
 - reflexivity.
 - reflexivity.
Qed.

Theorem plus_1_neq_v2 : forall n : nat,
 (n + 1) =? 0 = false.
Proof.
 intros [| n].
 - reflexivity.
 - reflexivity.
Qed.


Theorem andb_true_elim2 : forall b c : bool,
 andb b c = true -> c = true.
Proof.
  intros [] [].
  - simpl. reflexivity.
  - simpl. auto.
  - simpl. auto.
  - simpl. auto.
Qed.

Theorem identity_fn_applied_twice :
 forall (f : bool -> bool), 
 (forall (x: bool), f x = x) -> 
  forall (b : bool), f (f b) = b.
Proof.
 intros f.
 intros HA.
 intros b.
 rewrite -> HA.
 rewrite <- HA.
 reflexivity.
Qed.

Theorem negation_fn_applied_twice :
 forall (f : bool -> bool), 
 (forall (x: bool), f x = negb x) -> forall (b : bool), f (f b) = b.
Proof.
 intros f.
 intros H.
 intros b.
 (* right arrow means that (left is replaced by right) *)
 rewrite -> H.
 rewrite -> H.
 destruct b.
 simpl. reflexivity.
 simpl. reflexivity.
Qed.

Theorem andb_eq_orb:
 forall (b c: bool),
 (andb b c = orb b c) ->
 b = c.
Proof.
 intros [] [].
 simpl. reflexivity.
 simpl. intros. rewrite -> H. reflexivity.
 simpl. intros. rewrite -> H. reflexivity.
 simpl. intros. reflexivity.
Qed.

Theorem andb_eq_orb_v2:
 forall (b c: bool),
 (andb b c = orb b c) ->
 b = c.
Proof.
 intros [].
 intros [].
 intros H.
 reflexivity.
 simpl.
 intros H.
 rewrite H.
 reflexivity.
 intros [].
 simpl.
 intros [].
 reflexivity.
 simpl.
 intros [].
 reflexivity.
Qed.

Theorem andb_eq_orb_v3:
 forall (b c: bool),
 (andb b c = orb b c) ->
 b = c.
Proof.
 intros b c.
 destruct b.
 - simpl. intros H. rewrite H. reflexivity.
 - simpl. intros H. rewrite H. reflexivity.
Qed.

Inductive bin : Type :=
| Z
| B0 (n: bin)
| B1 (n: bin).

Fixpoint incr (m: bin) :=
match m with
| Z => B1 Z
| B0 n => B1 n
| B1 n => B0 (incr n)
end.

Fixpoint bin_to_nat (m: bin): nat :=
match m with
| Z => 0
| B0 n => 2 * (bin_to_nat n)
| B1 n => 2 * (bin_to_nat n) + 1
end.

Example z_inc: incr Z = B1 Z.
Proof. simpl. reflexivity. Qed.

Example one_inc: incr (incr Z)  = B0 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr2: (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.

Theorem add_0_r : forall n: nat,
 n + 0 = n.
Proof.
 intros n. 
 induction n as [| n' IHn'].
 - reflexivity.
 - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem minus_n_n: forall n,
 minus n n = 0.
Proof.
 intros n. induction n as [| n' IHn'].
 - simpl. reflexivity.
 - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mul_0_r: forall n: nat,
 n * 0 = 0.
Proof.
 intros n.
 induction n as [| n' IHn'].
 - simpl. reflexivity.
 - apply IHn'.
Qed.

Theorem plus_n_Sm: forall n m: nat,
 S (n + m) = n + (S m).



