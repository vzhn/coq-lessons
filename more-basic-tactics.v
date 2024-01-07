Require Import List.
Import ListNotations.

Import PeanoNat.Nat.



Theorem silly1: forall (n m: nat),
 n = m -> 
 n = m.
Proof.
 intros n m eq.
 apply eq. 
Qed.


Theorem silly2 : forall (n m o p : nat),
    n = m ->
    (n = m -> [n;o] = [m;p]) ->
    [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.  Qed.

Search "even".

Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true -> odd (S p) = true.
Proof.
 intros.
 apply H0.
 apply H.
 apply H1.
Qed.

Theorem silly3: forall (n m: nat),
 n = m -> m = n.
Proof.
 intros n m H.
 symmetry.
 apply H.
Qed.

Search "rev".

Theorem rev_involutive: forall X: Type, forall l: list X,
 rev (rev l) = l.
Proof.
 intros.
 induction l as [| lh' lt' IHl'].
 - reflexivity.
 - simpl.
   rewrite rev_app_distr.
   rewrite IHl'.
   reflexivity. 
Qed.

Theorem rev_exercise1: forall (l l': list nat),
 l = rev l' -> l' = rev l.
Proof.
 intros.
 symmetry.
 rewrite H.
 apply rev_involutive.
Qed.


Theorem trans_eq: forall (X: Type) (n m o: X),
 n = m -> m = o -> n = o.
Proof.
 intros X n m o eq1 eq2.
 rewrite -> eq1.
 rewrite -> eq2.
 reflexivity.
Qed.


Example trans_eq_example: forall (a b c d e f: nat),
 [a; b] = [c; d] ->
 [c; d] = [e; f] ->
 [a; b] = [e; f].
Proof.
 intros.
 apply trans_eq with ( m:=[c;d]).
 apply H.
 apply H0.
Qed.

Example trans_eq_example'': forall (a b c d e f: nat),
 [a; b] = [c; d] ->
 [c; d] = [e; f] ->
 [a; b] = [e; f].
Proof.
 intros a b c d e f eq1 eq2.
 transitivity [c; d].
 apply eq1.
 apply eq2.
Qed.

Search "minustwo".

Definition minustwo (n: nat) :=
match n with
| 0 => 0
| 1 => 0
| S (S n') => n'
end.

Example trans_eq_exercise: forall (n m o p: nat),
 m = (minustwo o) -> 
 (n + p) = m ->
 (n + p) = (minustwo o).
Proof.
 intros n m o p s1 s2.
 apply trans_eq with (m:=n+p).
 reflexivity.
 rewrite s2.
 rewrite s1.
 reflexivity.
Qed.

Theorem S_injective: forall (n m: nat),
 S n = S m -> n = m.
Proof.
 intros n m H.
 injection H as Hnm.
 apply Hnm. 
Qed.

Theorem injection_ex1: forall (n m o: nat),
 [n; m] = [o; o] -> n = m.
Proof.
 intros n m o eq1.
 injection eq1 as H1 H2.
 rewrite H1.
 rewrite H2.
 reflexivity.
Qed.

Example injection_ex3: forall (X: Type) (x y z: X) (l j: list X),
 x::y::l = z :: j ->
 j = z :: l ->
 x = y.
Proof.
 intros X x y z l j eq1.
 injection eq1 as H1 H2.
 rewrite <- H2.
 rewrite H1.
 intros eq2.
 injection eq2 as H3.
 rewrite H3.
 reflexivity.
Qed.

Theorem f_equal: forall (A B: Type) (f: A -> B) (x y: A),
 x = y -> f x = f y.
Proof.
 intros A B  f x y eq.
 rewrite eq.
 reflexivity.
Qed.

Theorem eq_implies_succ_equal: forall (n m: nat),
 n = m -> S n = S m.
Proof.
 intros n m H.
 apply f_equal.
 apply H.
Qed.

Theorem eq_implies_succ_equal': forall (n m: nat),
 n = m -> S n = S m.
Proof.
 intros n m H.
 f_equal.
 apply H.
Qed.

Theorem eqb_0_l: forall n,
 0 =? n = true -> n = 0.
Proof.
 intros n.
 destruct n as [| n'] eqn: E.
 - simpl. reflexivity.
 - simpl. intros H. discriminate H.
Qed.

Theorem S_inj: forall (n m: nat) (b: bool),
 ((S n) =? (S m) = b) -> (n =? m) = b.
Proof.
 intros n m b H.
 simpl in H.
 apply H.
Qed.

Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q EQ H.
  symmetry in H. apply EQ in H. symmetry in H.
  apply H. Qed.



Theorem specialize_example: forall n,
 (forall m, m * n = 0) -> n = 0.
Proof.
 intros n H.
 specialize H with (m := 1).
 simpl in H.
 rewrite add_comm in H.
 simpl in H.
 apply H.
Qed.

Example trans_eq_example''': forall (a b c d e f: nat),
 [a;b] = [c;d] ->
 [c;d] = [e;f] ->
 [a;b] = [e;f].
Proof.
 intros a b c d e f eq1 eq2.
 specialize trans_eq with (m := [c; d]) as H.
 apply H.
 apply eq1.
 apply eq2.
Qed.

Search "double".

Lemma double_001: forall (n: nat),
 double n = n + n.
Proof.
 induction n as [|n' IHn'].
 - reflexivity.
 - simpl. reflexivity.
Qed.





Lemma double_003: forall (n: nat),
 S (double n) = n + S n.
Proof.
 induction n as [|n' IHn'].
 - reflexivity.
 - simpl.
Admitted.



Theorem double_injective_take2 : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m.
  (* [n] and [m] are both in the context *)
  generalize dependent n.
  (* Now [n] is back in the goal and we can do induction on
     [m] and get a sufficiently general IH. *)
  induction m as [| m' IHm'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'.
      injection eq as goal. 
      rewrite add_comm in goal. simpl in goal.
      symmetry in goal.
      rewrite add_comm in goal. simpl in goal. 
      symmetry in goal.
      apply S_injective in  goal.
      apply goal.      
Qed. 

Search "length".

Theorem nth_error_after_last: forall (n: nat) (X: Type) (l: list X),
 length l = n -> nth_error l n = None.
Proof.
 intros.
 generalize dependent n.
 induction l as [|lh' lt' IHl'].
 - simpl.
   intros n H.
   symmetry in H.
   rewrite H.
   reflexivity.
 - intros n H.
   symmetry in H.
   rewrite H.
   simpl.
   apply IHl'.   
   reflexivity.
Qed.

Definition square n := n * n.


Lemma square_mult: forall n m, square (n * m) = square n * square m.
Proof.
 intros n m.
 unfold square.
 rewrite mul_assoc.
 assert (H: n * m * n = n * n * m).
 { rewrite mul_comm. apply mul_assoc. }
 rewrite H.
 rewrite mul_assoc.
 reflexivity.
Qed.

Definition foo (x: nat) := 5.
Fact silly_fact_1: forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
 intros m.
 unfold foo.
 reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. 
  unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity. Qed.

Theorem lists_lemma: forall X (a b: X),
 [a; b] <> [].
Proof.
 intros.
 discriminate.
Qed.

Search ((_, _) = (_, _)).

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.


Lemma split_lemma_002: forall X Y (a: (X * Y)) (tl: list (X * Y)),
 split (a::tl) <> ([], []).
Proof.
 intros.
 destruct a eqn:E1.
 unfold split.
Admitted.

Lemma split_lemma: forall X Y (l: list (X * Y)),
 split l = ([], []) -> l = [].
Proof.
 intros X Y l.
 destruct l.
 reflexivity.
 assert (H: not(split (p :: l) = ([], []))).
 { 
   simpl.
 }
Admitted.


Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
 intros X Y l l1 l2.
 generalize dependent l2.
 generalize dependent l1.


 induction l as [| lh lt IHl].
 - unfold split.
   intros l1 l2 H.
   apply pair_equal_spec in H.
   destruct H.
   rewrite <- H.
   rewrite <- H0.
   reflexivity.
 - intros. 
   inversion H.   
   destruct lh.
   destruct (split lt).
   inversion H1.
   simpl.
   apply f_equal.
   apply IHl.
   reflexivity.
Qed.

Search "eqb_true".

Theorem eqb_true: forall n m,
 n =? m = true -> n = m.
Proof.
 intros n m H.
 generalize dependent m.

 induction n as [|n'].
 - destruct m.
   reflexivity.
   discriminate.
 - destruct m as [|m'] eqn:E.
   discriminate.
   intros H1.

   specialize IHn' with (m:=m').
   rewrite IHn'.
   reflexivity.
   simpl in H1.
   rewrite H1.
   reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
  sillyfun1 n = true ->
  odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
  apply eqb_true in Heqe3.
  rewrite Heqe3.
  reflexivity.
  destruct (n =? 5) eqn:Heqe5.
  apply eqb_true in Heqe5.
  rewrite Heqe5.
  reflexivity.
  discriminate eq.
Qed.