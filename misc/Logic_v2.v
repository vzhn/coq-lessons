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

Search " _ <= _".
Require Import List.
Import ListNotations.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [ ] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORKED IN CLASS *)
  simpl. right. right. right. left. reflexivity.
Qed.

Search "n <=? n".

Search "_ \/ _ ".

Theorem leb_plus_exists: forall n m, n <=? m = true -> exists x, m = n + x.
Proof.
 intros n m.
 intros H.
 exists (m - n).
 rewrite add_sub_assoc.
 rewrite add_sub_swap.
 rewrite sub_diag.
 reflexivity.
 apply le_n.
 apply leb_le.
 apply H.
Qed.

Check False.

Lemma and_distrib: forall A B C: Prop,
 A /\ (B \/ C) <-> (A /\ B) \/ (A /\ C).
Proof.
 split.
 - simpl.
   intros H.
   destruct H.
   destruct H0.
   left.
   split.
   apply H.
   apply H0.
   right.
   split.
   apply H.
   apply H0.
 - intros. 
   apply conj.
   destruct H.
   destruct H.
   apply H.
   destruct H.
   apply H.
   destruct H.
   destruct H.
   left. apply H0.
   right.
   destruct H.
   apply H0.
Qed.


Theorem In_map_iff:
 forall (A B: Type) (f: A -> B) (l: list A) (y: B),
        In y (map f l) <->
        exists x, f x = y /\ In x l.
Proof.
 intros A B f l y.
 induction l as [|lh' lt'].
 - simpl. 
   split.
   intros H.
   contradiction.
   intros H.
   destruct H.
   apply proj2 in H.
   apply H.
 - split.
   simpl.   
   intros H1.
   destruct H1.
   exists lh'.
   split.
   apply H.
   left.
   reflexivity.
   destruct IHlt' as [IHA IHB].
   assert (H2: exists x : A, f x = y /\ In x lt').
   { apply IHA. apply H. }
   inversion H2.
   destruct H0.
   exists x.
   split.
   apply H0.
   right.
   apply H1.
   simpl.
   destruct IHlt' as [HA].
   intros H1.
   destruct H1.
   destruct H0.
   destruct H1.
   rewrite H1.
   left. apply H0.
   right. apply H.
   exists x.
   split.
   apply H0.
   apply H1.
Qed.


Theorem In_app_iff : forall A l l' (a: A),
  In a (l ++ l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
  - intros. simpl.
  split.
  intros H.
  right.
  apply H.
  intros H.
  destruct H.
  apply ex_falso_quodlibet.
  contradiction.
  apply H.
 - intros.
  simpl.
  split.
  intros H1.
  specialize IH with l'0 a.
  destruct IH.
  destruct H1.
  left. left. apply H1.
  apply H in H1.
  destruct H1.
  left. right.
  apply H1.
  right. apply H1.
  intros H.
  destruct H as [HA |HB].
  destruct HA.
  left.
  apply H.
  right.
  apply IH.
  left.
  apply H.
  right.
  apply IH.
  right.
  apply HB.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop := 
match l with
| [] => True
| lh::lt => P lh /\ All P lt
end.
 
Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
 intros.
 split.
 - induction l as [|lh lt IHl].
   + intros H. apply I.
   + simpl.
     intros H.
     simpl.
     split.
     specialize H with lh.
     apply H.
     left. reflexivity.  
     apply IHl.
     intros.
     apply H.
     right.
     apply H0.
 - induction l as [|lh lt IHl].
  + simpl.
    intros H x.
    apply ex_falso_quodlibet.
  + simpl.
    intros H.
    destruct H.
    intros x.
    intros H1.
    destruct H1.
    rewrite <- H1.
    specialize IHl with lh.
    apply H.
    specialize IHl with x.
    apply IHl in H0.
    apply H0.
    apply H1.
Qed.

Search "odd".

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
 fun n => if (odd n) then Podd n else Peven n.


Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
 intros.
 unfold combine_odd_even.
 destruct (odd n).
 apply H.
 reflexivity.
 apply H0.
 reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
 intros Podd.
 intros Peven.
 intros n.
 unfold combine_odd_even.
 intros H.
 intros HA.
 rewrite HA in H.
 apply H.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = false ->
    Peven n.
Proof.
 intros.
 unfold combine_odd_even in H.
 rewrite H0 in H.
 apply H.
Qed.

Lemma add_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  rewrite (add_comm y z).
  reflexivity.
Qed.

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
 intros.
 unfold not.
 intro Hl.
 rewrite Hl in H.
 simpl in H.
 apply H.
Qed.

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

Lemma in_not_nil_42_take4:
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.


Lemma in_not_nil_42_take5:
  forall l : list nat, In 42 l -> l <> [].
Proof.
intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Search " _ + _".

Lemma even_double : forall k, even (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - unfold double in IHk'.
    unfold double.
    rewrite <- IHk'.
    assert (H: S k' + S k' = S (S k') + k').
    { simpl. apply f_equal. rewrite <- plus_Sn_m. apply add_comm. }
    rewrite H.
    simpl.
    reflexivity.
Qed.

Import Bool.
Search negb.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
 intros.
 generalize dependent n.
 induction n as [|n' IHn'].
 - reflexivity.
 - rewrite IHn'. 
   simpl. rewrite negb_involutive.
   reflexivity.
Qed.

Search " _ + _".


Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  intros.
  induction n as [| n' IHn'].
  - exists 0. reflexivity.
  - destruct IHn'.
    rewrite even_S.
    destruct (even n').
    simpl.
    exists x.
    rewrite H.
    reflexivity.
    exists (S x).
    simpl.
    rewrite H.
    unfold double.
    simpl.
    apply f_equal.
    rewrite plus_n_Sm.
    reflexivity.
Qed.

Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intros n. split.
  - intros H. destruct (even_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply even_double.
Qed.
