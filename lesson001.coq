Require Import Arith.
Require Import Coq.Init.Peano.

Definition neg (b: bool): bool :=
match b with
| true => false
| false => true
end.

Definition and (b1: bool) (b2: bool): bool :=
match b1, b2 with
| true, true => true
| _, _ => false
end.

Definition nandb (b1:bool) (b2:bool) : bool :=
 (neg (and b1 b2)).

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Check true.

Check true : bool.
Check (negb true) : bool.

Inductive rgb: Type :=
| red
| green
| blue.

Inductive color : Type :=
| black
| white
| primary (p : rgb).


Fixpoint even (n: nat) : bool :=
match n with
| O => true
| S n' => neg (even n')
end.

Compute even 2.

Fixpoint add (a b: nat): nat :=
match a with
| O => b
| S a' => S (add a' b)
end.

Fixpoint mul (a b: nat): nat :=
match a with
| O => O
| S O => b
| S a' => add b (mul a' b)
end.

Example test_mul_3_2: (mul (S (S (S O))) (S (S O))) = 6.
Proof. simpl. reflexivity. Qed.

Fixpoint factorial (n: nat) : nat :=
match n with
| O => S O
| S n' => (mul n (factorial n'))
end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial10: (factorial 5) = 120.
Proof. simpl. reflexivity. Qed.

Theorem plus_0_n: forall n : nat, 0 + n = n.
Proof.
intros n.
reflexivity.
Qed.


Theorem plus_1_l : forall n: nat, 1 + n = S n.
Proof.
intros n.
reflexivity.
Qed.


Theorem plus_id_example : forall n m: nat,
 n = m ->
 n + n = m + m.
Proof.
intros n m.
intros H.
rewrite -> H.
reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
 n = m -> m = o -> n + m = m + o.
Proof.
intros n m o.
intros H.
rewrite -> H.
intros H2.
rewrite -> H2.
reflexivity.
Qed.


Check plus_1_l.

Locate "=?".

Theorem plus_1_neq_0_firsttry : forall n : nat,
 (n + 1) =? 0 = false.
Proof.
 intros n. destruct n as [| n'] eqn:E.
 - reflexivity.
 - reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
 negb (negb b) = b.
Proof.
 intros b.
 destruct b eqn:E.
 - reflexivity.
 - reflexivity.
Qed.

Theorem plus_id_example2 : forall n m:nat,
 n = m ->
 n + n = m + m.
Proof.
 intros n m.
 intros H.
 rewrite -> H.
 reflexivity.
Qed.


Check mult_n_O.
Check mult_n_Sm.

Theorem mult_n_0_m_0 : forall p q: nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. 
Qed.

Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
 intros p.
 
 destruct p as [| p'] eqn:E.
 simpl.
 reflexivity.
 rewrite <- mult_n_Sm.
 rewrite <- mult_n_O.
 simpl.
 reflexivity.
Qed.



Theorem andb_true_elim2 : forall b c : bool,
 andb b c = true -> c = true.
Proof.
 intros b c.
 destruct c.
 reflexivity.
 destruct b.
 simpl.
 intros.
 rewrite <- H.
 reflexivity.
 simpl.
 intros.
 rewrite <- H.
 simpl.
 reflexivity.
Qed.

Theorem andb_commutative'' :
 forall b c, andb b c = andb c b.
Proof.
 intros [] [].
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n: nat,
 0 =? (n + 1) = false.
Proof.
 intros [].
 - reflexivity.
 - reflexivity.
Qed.
 
Theorem identity_fn_applied_twice :
 forall (f : bool -> bool),
 (forall (x: bool), f x = x) ->
 forall (b: bool), f (f b) = b.
Proof.
 intros f.
 intros H.
 intros x.
 rewrite -> H.
 rewrite -> H.
 reflexivity.
Qed.


Theorem negation_fn_applied_twice :
 forall (f : bool -> bool),
 (forall (x: bool), f x = negb x) -> forall (b: bool), f (f b) = b.
Proof.
 intros f.
 intros H.
 intros b.
 rewrite -> H.
 rewrite -> H.
 destruct b.
 reflexivity.
 reflexivity.
Qed.

Theorem andb_eq_orb :
 forall (b c : bool),
 (andb b c = orb b c) -> b = c.
Proof.
 intros [] [].
 - simpl. intros B. reflexivity.
 - simpl. intros B. rewrite <- B. reflexivity.
 - simpl. intros B. rewrite <- B. reflexivity.
 - simpl. intros B. reflexivity.
Qed.

Module LateDays.

Inductive letter : Type :=
 | A | B | C | D | F.


Inductive modifier: Type :=
 | Plus | Natural | Minus.

Inductive grade : Type :=
 Grade (l: letter) (m: modifier).

Inductive comparison : Type :=
 | Eq
 | Lt
 | Gt.

Definition letter_comparison (l1 l2 : letter) : comparison :=
  match l1, l2 with
  | A, A => Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, (A | B) => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, (A | B | C) => Lt
  | D, D => Eq
  | D, _ => Gt
  | F, (A | B | C | D) => Lt
  | F, F => Eq
  end.

Theorem letter_comparison_eq : (forall n: letter, letter_comparison n n = Eq).
Proof.
 intros n.
 destruct n.
 - simpl. reflexivity.
 - simpl. reflexivity.
 - simpl. reflexivity.
 - simpl. reflexivity.
 - simpl. reflexivity.
Qed.

Definition modifier_comparison (m1 m2 : modifier) : comparison :=
  match m1, m2 with
  | Plus, Plus => Eq
  | Plus, _ => Gt
  | Natural, Plus => Lt
  | Natural, Natural => Eq
  | Natural, _ => Gt
  | Minus, (Plus | Natural) => Lt
  | Minus, Minus => Eq
  end.

Definition grade_comparison (g1 g2 : grade): comparison :=
 match g1 with
  | (Grade a1 b1) => match g2 with
                   | (Grade a2 b2) => match letter_comparison a1 a2 with
                                     | Eq => modifier_comparison b1 b2
                                     | Lt => Lt
                                     | Gt => Gt
                                     end
                   end
 end.

Example test_grade_comparison1: (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
Proof. simpl. reflexivity. Qed.

Example test_grade_comparison2 :
  (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
Proof. simpl. reflexivity. Qed.

Example test_grade_comparison3 :
  (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
Proof. simpl. reflexivity. Qed.

Example test_grade_comparison4 :
  (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
Proof. simpl. reflexivity. Qed.

Definition lower_letter (l : letter) : letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F (* Can't go lower than F! *)
  end.

Theorem lower_letter_F_is_F:
 lower_letter F = F.
Proof.
 simpl. reflexivity.
Qed.

Compute letter_comparison F F.

Theorem lower_letter_lowers:
 forall (l : letter),
   letter_comparison F l = Lt ->
   letter_comparison (lower_letter l) l = Lt.
Proof.
 destruct l.
 - simpl. intros H. reflexivity.
 - simpl. intros H. reflexivity.
 - simpl. intros H. reflexivity.
 - simpl. intros H. reflexivity.
 - simpl. intros H. rewrite <- H. reflexivity.
Qed.

Definition lower_grade (g: grade) : grade :=
match g with
| Grade letter modifier => match modifier with
                           | Plus => Grade letter Natural
                           | Natural => Grade letter Minus
                           | Minus => match letter with
                                      | F => Grade F Minus 
                                      | _ => Grade (lower_letter letter) Plus 
                                      end
                           end
end.

Example lower_grade_A_Plus :
  lower_grade (Grade A Plus) = (Grade A Natural).
Proof. reflexivity. Qed.

Example lower_grade_A_Natural :
  lower_grade (Grade A Natural) = (Grade A Minus).
Proof. reflexivity. Qed.


Example lower_grade_A_Minus :
  lower_grade (Grade A Minus) = (Grade B Plus).
Proof. reflexivity. Qed.

Example lower_grade_B_Plus :
  lower_grade (Grade B Plus) = (Grade B Natural).
Proof. reflexivity. Qed.


Example lower_grade_F_Natural :
  lower_grade (Grade F Natural) = (Grade F Minus).
Proof. reflexivity. Qed.

Example lower_grade_twice :
  lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
Proof. reflexivity. Qed.

Example lower_grade_thrice :
  lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
Proof. reflexivity. Qed.


Theorem lower_grade_F_Minus : lower_grade (Grade F Minus) = (Grade F Minus).
Proof. reflexivity. Qed.

Theorem letter_comparison_Eq :
  forall l, letter_comparison l l = Eq.
Proof.
 intros l.
 destruct l.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
Qed.


Theorem lower_grade_lowers:
 forall (g: grade),
   grade_comparison (Grade F Minus) g = Lt ->
   grade_comparison (lower_grade g) g = Lt.
Proof.
 intros g.
 intros H.
 destruct g.
 destruct m.
 - simpl.  rewrite -> letter_comparison_Eq. reflexivity.
 - simpl.  rewrite -> letter_comparison_Eq. reflexivity.
 - simpl. destruct l.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. rewrite <- H. simpl. reflexivity.
Qed.
 
 
Inductive bin : Type :=
 | Z
 | B_0 (n : bin)
 | B_1 (n : bin).

Fixpoint incr(m: bin): bin :=
match m with
| Z => B_1 Z
| B_0 n' => B_1 n'
| B_1 n' => B_0 (incr n') 
end.

Fixpoint bin_to_nat (b: bin): nat :=
match b with
| Z => 0
| B_0 n' => 2 * (bin_to_nat n')
| B_1 n' => 2 * (bin_to_nat n') + 1
end.


Example test_bin_incr1 : (incr (B_1 Z)) = B_0 (B_1 Z).
Proof. reflexivity. Qed.

Example test_bin_incr2 : (incr (B_0 (B_1 Z))) = B_1 (B_1 Z).
Proof. reflexivity. Qed.
Example test_bin_incr3 : (incr (B_1 (B_1 Z))) = B_0 (B_0 (B_1 Z)).
Proof. reflexivity. Qed.
Example test_bin_incr4 : bin_to_nat (B_0 (B_1 Z)) = 2.
Proof. reflexivity. Qed.
Example test_bin_incr5 : bin_to_nat (incr (B_1 Z)) = 1 + bin_to_nat (B_1 Z).
Proof. reflexivity. Qed.
Example test_bin_incr6 : bin_to_nat (incr (incr (B_1 Z))) = 2 + bin_to_nat (B_1 Z).
Proof. reflexivity. Qed.

End LateDays .

Theorem add_0_r : forall n: nat,
 n + 0 = n.
Proof.
 intros n. induction n as [| n' IHn'].
 - reflexivity.
 - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem minus_n_n: forall n: nat,
 minus n n = 0.
Proof.
 intros n. induction n as [| n' IHn'].
 - reflexivity.
 - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mul_0_r: forall n: nat,
 n * 0 = 0.
Proof.
 intros n. induction n as [| n' IHn'].
 - simpl. reflexivity.
 - simpl. rewrite -> IHn'. reflexivity. 
Qed.

Theorem plus_n_Sm: forall n m : nat,
 S (n + m) = n + (S m).
Proof. 
 intros n. induction n as [| n' IHn'].
 - simpl. reflexivity.
 - intros m. simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_comm: forall n m: nat,
 n + m = m + n.
Proof.
 intros n m.
 induction n as [| n' IHn']. 
 - simpl. induction m. simpl. reflexivity. simpl. rewrite <- IHm. reflexivity.
 - simpl. rewrite <-plus_n_Sm. rewrite <- IHn'. reflexivity.
Qed.
 
Theorem add_assoc: forall n m p : nat,
 n + (m + p) = (n + m) + p.
Proof.
 intros m.
 induction m as [| m' IHm']. 
 - simpl. 
   reflexivity.
 - simpl. 
   intros m p. 
   rewrite -> IHm'. 
   reflexivity.
Qed.

Theorem eqb_refl : forall n : nat,
 (n =? n) = true.
Proof.
 intros n.
 induction n as [| n' IHn'].
 - simpl. reflexivity.
 - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem even_S : forall n : nat,
 even (S n) = negb (even n).
Proof.
 intros n.
 induction n as [| n' IHn'].
 - simpl. reflexivity.
 - simpl. destruct neg. 
   + simpl. reflexivity.
   + simpl. reflexivity.
Qed.

Theorem add_shuffle3 : forall n m p : nat,
 n + (m + p) = m + (n + p).
Proof.
 intros n m p.
 rewrite -> add_comm.
 rewrite <- add_assoc.
 assert (H: p + n = n + p).
 { rewrite add_comm. reflexivity. }
 rewrite H. reflexivity.
Qed.

Theorem plus_rearrange: forall n m p q : nat,
 (n + m) + (p + q) = (m + n) + (p + q).
Proof.
 intros n m p q.
 assert (H: n + m = m + n).
 { rewrite add_comm. reflexivity. }
 rewrite H. reflexivity.
Qed.

Theorem mul_1: forall m: nat,
 m * 1 = m.
Proof.
 intros m.
 induction m as [| m' IHm'].
 - simpl. reflexivity.
 - simpl. rewrite -> IHm'. reflexivity.
Qed.

Theorem add_1: forall n: nat,
 n + 1 = S n.
Proof.
 intros n.
 induction n as [| n' IHn'].
 - reflexivity.
 - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem add_0: forall n: nat,
 n + 0 = n.
Proof.
 intros n. 
 rewrite add_comm.
 simpl. reflexivity.
Qed.


Theorem add_lemma_001: forall a b c: nat,
 a + c + b = a + b + c.
Proof.
 intros a b c.
 induction a as [| a' IHa'].
 - simpl. rewrite add_comm. reflexivity.
 - rewrite <- add_1. rewrite add_1. simpl. rewrite IHa'. reflexivity. 
Qed.

Theorem add_lemma_002: forall a b: nat,
 S (a + b) = a + S b.
Proof.
 intros a b.
 induction a as [| a' IHa'].
 - simpl. reflexivity.
 - simpl. rewrite IHa'. simpl. reflexivity.
Qed.

Theorem mul_n_0: forall n: nat,
 n * 0 = 0.
Proof.
 intros n.
 induction n.
 - simpl. reflexivity.
 - simpl. rewrite IHn. reflexivity.
Qed.

Theorem add_lemma_003: forall a b: nat,
 a + a + b =  a + b + a.
Proof.
 intros a b.
 assert (H: a + b = b + a).
 { rewrite add_comm. reflexivity. }
 rewrite add_comm.
 rewrite <- add_shuffle3.
 rewrite <- add_comm.
 rewrite <- H.
 reflexivity.
Qed.




Theorem mul_lemma_001: forall a b: nat,
 (S a) * b = a * b + b.
Proof.
 intros a b.
 induction a as [| a' IHa'].
 - simpl. rewrite add_0. reflexivity.
 - simpl. rewrite add_assoc. rewrite add_lemma_003. reflexivity.
Qed.


Theorem add_lemma_004: forall a b: nat,
 a + (S b) = (S a) + b.
Proof.
 intros a b.
 assert (H: a + S b = a + b + 1).
 { rewrite <- add_1. rewrite <- add_assoc. reflexivity. }
 rewrite H.
 rewrite <- add_lemma_001.
 rewrite -> add_1. reflexivity.
 
Qed.


Theorem mul_lemma_002: forall a b: nat,
 a * (S b) = a * b + a.
Proof.
 intros a b.
 induction a as [| a' IHa'].
 - simpl. reflexivity.
 - rewrite mul_lemma_001. rewrite IHa'.
   rewrite mul_lemma_001. rewrite  add_lemma_004.
   rewrite add_lemma_002.
   rewrite <- add_1.
   rewrite add_lemma_001.
   reflexivity.
Qed.

Theorem mul_comm: forall m n : nat,
 m * n = n * m.
Proof.
 intros n m.
 induction n as [|n' IHn'].
 - simpl. rewrite mul_n_0. reflexivity.
 - rewrite mul_lemma_001.
   rewrite IHn'.
   rewrite mul_lemma_002.
   reflexivity. 
Qed.

Check leb.

Lemma leb_helper_001: forall n: nat,
 n <=? n = true.
Proof.
 intros n.
 induction n as [|n' IHn'].
 - simpl. reflexivity.
 - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_leb_compat_l : forall n m p: nat,
 n <=? m = true -> (p + n) <=? (p + n) = true.
Proof.
 intros n m p.
 intros H.
 
 induction p as [|p' IHp'].
 - simpl. rewrite leb_helper_001. reflexivity.
 - simpl. rewrite IHp'. reflexivity.
Qed.

Theorem leb_refl : forall n: nat,
 (n <=? n) = true.
Admitted.

Inductive natprod : Type :=
 | pair (n1 n2: nat).

Check (pair 3 5) : natprod.

Definition fst (p: natprod) : nat :=
 match p with
 | pair x y => x
 end.

Definition snd (p: natprod) : nat :=
 match p with
 | pair x y => y
 end.

Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (3, 5)).

Definition fst' (p: natprod) : nat :=
 match p with
 | (x, y) => x
 end.

Definition snd' (p: natprod) : nat :=
 match p with
 | (x, y) => y
 end.

Definition swap_pair (p: natprod): natprod :=
 match p with
 | (x, y) => (y, x)
 end.


Theorem surjective_pairing' : forall (n m: nat),
 (n, m) = (fst (n, m), snd (n, m)).
Proof. reflexivity. Qed.

Theorem surjective_pairing_stuck : forall (p: natprod),
 p = (fst p, snd p).
Proof.
 intros p.
 destruct p as [m n].
 simpl. reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p: natprod),
 (snd p, fst p) = swap_pair p.
Proof.
 intros k.
 destruct k as [m n].
 simpl.
 reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p: natprod),
 fst (swap_pair p) = snd p.
Proof.
 intros p.
 destruct p as [m n].
 simpl.
 reflexivity.
Qed.

Inductive natlist : Type :=
 | nil
 | cons (n: nat) (l: natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1; 2; 3].

Fixpoint repeat (n count: nat): natlist :=
 match count with
 | O => nil
 | S count' => n :: (repeat n count')
 end.

Fixpoint length (l: natlist): nat :=
 match l with
 | nil => 0
 | head :: tail => 1 + length tail
 end.

Fixpoint app (l1 l2: natlist): natlist :=
match l1 with
| nil => l2
| head :: tail => head :: (app tail l2)
end.

Compute app [1; 2; 3 ] [ 4; 5; 6; 7 ].

Notation " x ++ y " := (app x y)
                       (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.

Example test_app2: nil ++ [4; 5] = [4; 5].
Proof. reflexivity. Qed.

Definition hd (default: nat) (l: natlist): nat :=
 match l with
 | nil => default
 | h :: t => h
 end.

Definition tl (l: natlist): natlist :=
 match l with
 | nil => nil
 | h :: t => t
 end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.

Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.

Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l: natlist): natlist :=
match l with
| nil => nil
| 0 :: t => nonzeros t
| h :: t => h :: (nonzeros t)
end.

Example test_nonzeros:
 nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.


Fixpoint odd (n: nat): bool :=
match n with
| 0 => false
| S n' => negb (odd n')
end.

Fixpoint oddmembers (l: natlist): natlist :=
match l with
| nil => nil
| h :: t => match (odd h) with
            | true => h :: (oddmembers t)
            | false => oddmembers t
            end
end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. simpl. reflexivity. Qed.

Definition countoddmembers (l: natlist): nat := 
 length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. simpl. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. simpl. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. simpl. reflexivity. Qed.



Fixpoint alternate (l1 l2: natlist): natlist :=
match l1, l2 with
| nil, nil => nil
| nil, b   => b
| b,   nil => b
| ha::ta, hb::tb => ha :: hb :: alternate ta tb
end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.
Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v: nat) (s: bag): nat :=
match s with
| h :: t => match (h =? v) with
            | true => 1 + (count v t)
            | _ => count v t
            end
| nil => 0
end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition bag_add (v: nat) (s: bag): bag := v :: s.


Example test_add1: count 1 (bag_add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Example test_add2: count 5 (bag_add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint member (v: nat) (s: bag): bool :=
match s with
| head :: tail => match (head =? v) with
                  | true => true
                  | false => member v tail
                  end
| nil => false
end.

Example test_member1: member 1 [1;4;1] = true.
Proof. simpl. reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_one (v: nat) (s: bag): bag :=
match s with
| head :: tail => match (head =? v) with
                  | true => tail
                  | false => head :: (remove_one v tail)
                  end 
| nil => nil
end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v: nat) (s: bag): bag :=
match s with
| head :: tail => match (head =? v) with
                  | true => remove_all v tail
                  | false => head :: (remove_all v tail)
                  end 
| nil => nil
end.


Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.

Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint included (s1: bag) (s2: bag): bool :=
match s1 with
| head :: tail => match (member head s2) with
                  | true => included tail (remove_one head s2)
                  | false => false
                  end
| nil => true
end.

Example test_included1: included [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.

Example test_included2: included [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Theorem add_value_to_bag: forall (v: nat) (b: bag),
length b + 1 = length (v :: b).
Proof.
intros v b.
induction b as [|head tail IHb'].
- simpl. reflexivity.
- simpl. assert (H: (length tail) + 1 = S (length tail)).
 { rewrite add_1. reflexivity. }  
 rewrite H. reflexivity.
Qed.

Theorem nil_app: forall l: natlist,
 [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred: forall l: natlist,
 pred (length l) = length (tl l).
Proof.
 intros l.
 destruct l as [| n l'].
 - reflexivity.
 - reflexivity. Qed.

Theorem app_assoc: forall a b c: natlist, (a ++ b) ++ c = a ++ (b ++ c).
Proof.
intros a b c.
induction a as [| h t IHl1'].
- simpl. reflexivity.
- simpl.
  rewrite IHl1'.
  reflexivity.
Qed.

Fixpoint rev (l: natlist): natlist :=
 match l with
 | nil => nil
 | h :: t => rev t ++ [h]
 end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.

Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem app_length: forall a b: natlist,
length (a ++ b) = length a + length b.
Proof.
 intros a b.
 induction a as [| ah' at' IHa'].
 - reflexivity.
 - simpl. rewrite -> IHa'. reflexivity.
Qed.

Theorem rev_length_firsttry : forall l: natlist,
 length (rev l) = length l.
Proof.
 intros l.
 induction l as [| n l' IHl'].
 - reflexivity.
 - simpl.
   rewrite <- IHl'.
   rewrite app_length.
   simpl.
   rewrite add_1.
   reflexivity.
Qed.

Search rev.
Search (_ + _ = _ + _).
Search (?x + ?y = ?y + ?x).

Lemma app_001: forall (a: nat) (b c: natlist),
 (a :: b) ++ c = a :: (b ++ c).
Proof.
 intros a b c.
 induction b as [|bh' bt' IHb'].
 - simpl. reflexivity.
 - simpl. reflexivity.
Qed.


Theorem app_nil_r: forall l: natlist,
 l ++ [] = l.
Proof.
 intros l.
 induction l as [| lh' lt' IHl].
 - reflexivity.
 - rewrite app_001.
   rewrite IHl.
   reflexivity.
Qed.

Lemma rev_001: forall (a: nat) (l: natlist),
 rev (a::l) = rev l ++ a::nil.
Proof.
 intros a l.
 induction l as [| lh' lt' IHl].
 - simpl.
   reflexivity.
 - simpl.
   reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2: natlist,
 rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
 intros l1 l2.
 induction l1 as [| l1h' l1t' IHl1].
 - simpl.
   rewrite app_nil_r.
   reflexivity.
 - rewrite -> app_001.
   simpl. rewrite <- rev_001.
   simpl. rewrite IHl1.
   rewrite app_assoc.
   reflexivity.
Qed.

Theorem rev_involutive: forall l: natlist,
 rev (rev l) = l.
Proof.
 intros l.
 induction l as [| lh' lt' IHl'].
 - reflexivity.
 - simpl.
   rewrite rev_app_distr.
   rewrite IHl'.
   reflexivity.
Qed.

Theorem app_assoc4: forall a b c d: natlist,
 a ++ (b ++ (c ++ d)) = (((a ++ b) ++ c) ++ d).
Proof.
 intros a b c d.
 induction a as [| ah' at' IHa'].
 - simpl.
   rewrite app_assoc.
   reflexivity.
 - simpl.
   rewrite IHa'.
   reflexivity.
Qed.

Lemma nonzeros_app: forall l1 l2: natlist,
 nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
 intros l1 l2.
 induction l1 as [| l1h l1t IHl1'].
 - reflexivity.
 - destruct l1h.
   simpl.
   rewrite IHl1'.
   reflexivity.
   simpl.
   rewrite IHl1'.
   reflexivity.  
Qed.

Fixpoint eqblist (l1 l2: natlist): bool :=
 match l1, l2 with
 | l1h::l1t, l2h::l2t => (l1h =? l2h) && eqblist l1t l2t
 | nil, l2h::l2t => false
 | l1h::l1t, nil => false
 | nil, nil => true
 end.

Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. simpl. reflexivity. Qed.

Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. simpl. reflexivity. Qed.

Lemma nat_refl:
 forall n: nat,
 true = (n =? n).
Proof.
 intros l.
 induction l as [| l' IHl'].
 - reflexivity.
 - simpl. rewrite IHl'.
   reflexivity.
Qed.


Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. simpl. reflexivity. Qed.

Theorem eqblist_refl: forall l: natlist,
 true = eqblist l l.
Proof.
 intros l.
 induction l as [|lh lt IHl].
 - reflexivity.
 - simpl.
   rewrite <- IHl.
   simpl. rewrite <- nat_refl.
   reflexivity.
Qed.

Theorem leb_n_Sn: forall n,
 n <=? (S n) = true.
Proof.
 intros n.
 induction n as [| n' IHn'].
 - reflexivity.
 - simpl. rewrite IHn'. reflexivity.
Qed.


Theorem remove_does_not_increase_count: forall (s: bag),
 (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
 intros s.
 induction s as [| sh st IHs].
 - reflexivity.
 - rewrite <- IHs.
   simpl.
   destruct sh.
   rewrite leb_n_Sn.
   rewrite IHs. 
   reflexivity.
   simpl. reflexivity.
Qed.

Theorem bag_count_sum: forall (b1 b2: bag),
 count 0 (sum b1 b2) = (count 0 b1) + (count 0 b2).
Proof.
 intros b1 b2.
 induction b1 as [|b1h b1t IHb1].
 - reflexivity.
 - simpl.
   rewrite IHb1. 
   destruct b1h.
   reflexivity.
   simpl.
   reflexivity. 
Qed.

Theorem involution_injective: forall (f: nat -> nat),
 (forall n: nat, n = f (f n)) -> (forall n1 n2: nat, f n1 = f n2 -> n1 = n2).
Proof.
 intros f H.
 intros n n1.
 intros H0. 
 rewrite H.
 rewrite <- H0.
 rewrite <- H.
 reflexivity.
Qed.

Theorem rev_injective: forall (l1 l2: natlist),
 rev l1 = rev l2 -> l1 = l2.
Proof.
 intros l1 l2.
 intros H.
 rewrite <- rev_involutive.
 rewrite <- H.
 rewrite -> rev_involutive.
 reflexivity.
Qed.


Inductive natoption: Type :=
 | Some (n: nat)
 | None.

Fixpoint nth_error (l: natlist) (n: nat): natoption :=
match l with
| nil => None
| ha::ht => match n with
            | 0 => Some ha
            | S n' => nth_error ht n'
            end
end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

Definition option_elim (d: nat) (o: natoption): nat :=
match o with
| Some n => n
| None => d
end.

Definition hd_error (l: natlist): natoption :=
match l with
| nil => None
| hd::_ => Some hd
end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.

Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd: forall (l: natlist) (default: nat),
 hd default l = option_elim default (hd_error l).
Proof.
 intros l default.
 destruct l.
 - reflexivity. 
 - simpl. reflexivity.
Qed.

Inductive id : Type :=
 | Id (n: nat).

Definition eqb_id (x1 x2: id) :=
match x1, x2 with
| Id n1, Id n2 => n1 =? n2
end.

Search "x1 =? x1".

Theorem eqb_id_refl: forall x, eqb_id x x = true.
Proof.
intros x.
destruct x.
simpl.
rewrite <- nat_refl.
reflexivity.
Qed.

Inductive partial_map: Type :=
| empty
| record (i: id) (v: nat) (m: partial_map).

Definition update (d: partial_map)
                  (x: id) (value: nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x: id) (d: partial_map): natoption :=
match d with
| empty => None
| record y v d' => if eqb_id x y
                   then Some v
                   else find x d'
end.

Theorem update_eq:
 forall (d: partial_map) (x: id) (v: nat),
   find x (update d x v) = Some v.
Proof.
 intros d x v.
 destruct d.
 simpl.
 rewrite eqb_id_refl.
 reflexivity.
 simpl.
 rewrite eqb_id_refl.
 reflexivity.
Qed.

Theorem update_neq:
 forall (d: partial_map) (x y: id) (o: nat),
  eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
 intros d x y o.
 destruct d.
 intros H.
 simpl.
 rewrite H. reflexivity.
 intros H.
 simpl. rewrite H.
 reflexivity.
Qed.



