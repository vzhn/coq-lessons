Require Import PeanoNat.
Import PeanoNat.Nat.

Check (forall n m: nat, n + m = m + n): Prop.

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Search False.

Theorem zero_not_one: 0 <> 1.
Proof.
 unfold not.
 intros contra.
 discriminate contra.
Qed.
 
Theorem not_False :
  not False.
Proof.
  unfold not. intros H. destruct H. Qed.


Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ (not P)) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNA]. 
  unfold not in HNA.
  apply HNA in HP. 
  destruct HP. 
Qed.

Theorem double_neg_th: forall P: Prop,
 P -> not (not P).
Proof.
 intros P H.
 unfold not.
 intros G.
 apply G.
 apply H. 
Qed.

Theorem contrapositive: forall (P Q: Prop),
 (P -> Q) -> (not Q -> not P).
Proof.
 intros P Q.
 intros H1.
 intros H2.
 unfold not in H2.
 unfold not.
 intros HP.
 apply H2.
 apply H1.
 apply HP.
Qed.

Theorem not_both_true_and_false: forall P: Prop,
 not (P /\ not P).
Proof.
 intros P.
 unfold not.
 intros [HA HB].
 apply HB.
 apply HA.
Qed.

Check not True.

Theorem de_morgan_not_or: forall (P Q: Prop),
 not (P \/ Q) -> (not P /\ not Q).
Proof.
 intros P Q HA.
 unfold not in HA.
 unfold not.
 split.
 - intros HP.
   destruct HA.
   apply or_intro_l.
   apply HP.
 - intros A.
   destruct HA.
   apply or_comm.
   apply or_intro_l.
   apply A.
Qed.

Search "add_comm".

Example and_exercise:
 forall n m: nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
 intros n m H.  

 destruct n.
 simpl in H.
 rewrite H.
 apply conj.
 reflexivity.
 reflexivity.
 apply conj.
 discriminate.
 destruct m.
 reflexivity.
 discriminate.
Qed.

Lemma mult_is_O:
 forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
 intros n m H.
 destruct n.
 left.
 reflexivity.
 destruct m.
 right.
 reflexivity.
 discriminate.
Qed.

Theorem or_commut: forall P Q: Prop,
 P \/ Q -> Q \/ P.
Proof.
 intros P Q H.
 destruct H.
 right.
 apply H.
 left.
 apply H.
Qed.

Theorem ex_falso_quodlibet : forall (P: Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra. Qed.


Theorem not_true_is_false: forall b: bool,
 b <> true -> b = false.
Proof.
 intros b H.
 destruct b eqn:HE.
 - unfold not in H.
   apply ex_falso_quodlibet.
   apply H. reflexivity.
 - reflexivity.
Qed.

Lemma True_is_true: True.
Proof. apply I. Qed.

Definition disc_fn (n: nat): Prop :=
 match n with
 | O => True
 | S _ => False
 end.

Theorem disc_example: forall n, not (0 = S n).
Proof.
 intros n H1.
 assert (H2: disc_fn 0). { simpl. apply I. }
 rewrite H1 in H2.
 simpl in H2.
 apply H2.
Qed.

Theorem iff_sym: forall P Q: Prop,
 (P <-> Q) -> (Q <-> P).
Proof.
 intros P Q.
 intros [HAB HBA].
 split.
 apply HBA.
 apply HAB.
Qed.


Theorem or_distributes_over_and: forall P Q R: Prop,
 P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
 intros.
 split.
 - split.
   destruct H.
   left.
   apply H.
   destruct H.
   right.
   apply H.
   destruct H.
   left.
   apply H.
   destruct H.
   right.
   apply H0.
 - intros [H0 H1].
   destruct H0 as [HA|HD].
   destruct H1 as [HB|HC].
   left.
   apply HA.
   left.
   apply HA.
   destruct H1 as [HB|HC].
   left.
   apply HB.
   right.
   split.
   apply HD.
   apply HC.
Qed.


Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     n = 0 ∨ m = 0 *)
  intros n m [Hn | Hm].
  - (* Here, n = 0 *)
    rewrite Hn. reflexivity.
  - (* Here, m = 0 *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma mul_eq_0: forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
 split.
 - apply mult_is_O.
 - apply factor_is_O.
Qed.

Definition Even x := exists n: nat, x = double n.

Lemma four_is_Even: Even 4.
Proof.
  unfold Even.
  exists 2.
  reflexivity.
Qed.

Theorem exists_example_2: forall n,
 (exists m, n = 4 + m) ->
 (exists o, n = 2 + o).
Proof.
 intros n [m Hm].
 exists (2 + m).
 apply Hm.
Qed.

Theorem dist_not_exists: forall (X: Type) (P: X -> Prop),
 (forall x, P x) -> not (exists x, not (P x)).
Proof.
 intros.
 unfold not. 
 intros.
 destruct H0.
 specialize (H x).
 destruct H0.
 apply H.
Qed.

Theorem dist_exists_or : forall (X: Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
 intros.
 split.
 intros HA.
 destruct HA.
 destruct H.
 left.
 exists x.
 apply H.
 right.
 exists x.
 apply H.
 intros H.
 destruct H.
 destruct H.
 exists x.
 left.
 apply H.
 destruct H.
 exists x.
 right.
 apply H.
Qed.




Theorem leb_plus_exists: forall n m, n <=? m = true -> exists x, m = n + x.
Proof.
 intros n m.
 induction m as [|mh mtl].
 destruct n.
 simpl.
 intros H.
 exists 0.
 reflexivity.
 discriminate.
 assert (H: n <=? mh = true -> n <=? S mh = true ).
 { intros H1. }
 destruct H.
Qed.
