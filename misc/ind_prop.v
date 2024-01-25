Import Nat.
Require Import PeanoNat.
Import PeanoNat.Nat.
Require Import List.
Import ListNotations.
Import List.

Fixpoint div2 (n : nat) :=
  match n with
    0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Definition f (n : nat) :=
  if even n then div2 n
  else (3 * n) + 1.

Inductive Collatz_holds_for : nat -> Prop :=
  | Chf_done : Collatz_holds_for 1
  | Chf_more (n : nat) : Collatz_holds_for (f n) -> Collatz_holds_for n.

Example Collatz_holds_for_12 : Collatz_holds_for 12.
Proof.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_done.
 Qed.

Conjecture collatz : forall n, Collatz_holds_for n.

Search le_S.

Reserved Notation "n <= m" (at level 70).
Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : n <= n
  | le_S (n m : nat) : n <= m -> n <= (S m)

  where "n <= m" := (le n m).

Example le_3_5 : 3 <= 5.
Proof.
  apply le_S. apply le_S. apply le_n. Qed.

Inductive clos_trans {X: Type} (R: X ->X -> Prop) : X -> X -> Prop :=
  | t_step (x y : X) :
      R x y ->
      clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y ->
      clos_trans R y z ->
      clos_trans R x z.

Inductive cols_reflexive_trans {X: Type} (R: X -> X -> Prop): X -> X -> Prop :=
| rt_step (x y: X): R x x /\ R y y -> cols_reflexive_trans R x y
| rt_trans (x y z: X): cols_reflexive_trans R x y -> cols_reflexive_trans R y z -> cols_reflexive_trans R x z
.


Inductive Person : Type := Sage | Cleo | Ridley | Moss.

Inductive parent_of : Person -> Person -> Prop :=
  po_SC : parent_of Sage Cleo
| po_SR : parent_of Sage Ridley
| po_CM : parent_of Cleo Moss.

Check parent_of.

Definition ancestor_of : Person -> Person -> Prop :=
  clos_trans parent_of.

Example ancestor_of1 : ancestor_of Sage Moss.
Proof.
  unfold ancestor_of. apply t_trans with Cleo.
  - apply t_step. apply po_SC.
  - apply t_step. apply po_CM. Qed.

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

Example Perm3_example1 : Perm3 [1;2;3] [2;3;1].
Proof.
  apply perm3_trans with [2;1;3].
  - apply perm3_swap12.
  - apply perm3_swap23. Qed.

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. 
  simpl. 
  intros Hn. 
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

Search "_ + _".

Theorem ev_double : forall n, ev (double n).
Proof.
 intros.
 induction n as [|n' IHn'].
 - apply ev_0.
 - unfold double.
   rewrite plus_Sn_m.
   rewrite <- add_succ_comm.
   rewrite plus_Sn_m.
   apply ev_SS .
   unfold double in IHn'.
   apply IHn'.
Qed.

Theorem ev_inversion: forall (n: nat),
 ev n -> (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
 intros n E.
 destruct E as [| n' E'] eqn:EE.
 - left. reflexivity.
 - right. exists n'. split. reflexivity. apply E'.
Qed.

Theorem evSS_ev: forall n, ev (S (S n)) -> ev n.
Proof.
 intros n H.
 apply ev_inversion in H.
 destruct H as [H0|H1].
 - discriminate H0.
 - destruct H1 as [n' [Hnm Hev]]. injection Hnm as Heq.
   rewrite Heq. apply Hev.
Qed.

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E as [| n' E' Heq].
  (* We are in the E = ev_SS n' E' case now. *)
  apply E'.
Qed.

Theorem one_not_even : not (ev 1).
Proof.
  intros H. apply ev_inversion in H. destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : not (ev 1).
Proof.
  intros H. inversion H. Qed.

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  inversion H as [|n' H0 H1].
  inversion H0 as [|n'' H2 H3].
  apply H2.
Qed.

SearchPattern (S _ =  _).

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
 intros H.
 inversion H.
 inversion H1.
 inversion H3.
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra.
  inversion contra. 
Qed.

Check add_comm.

Lemma ev_Even: forall n,
 ev n -> Even n.
Proof.
 intros n E.
 induction E as [|n' E' IH].
 - unfold Even. exists 0. reflexivity.
 - unfold Even in IH.
   destruct IH as [k Hk].
   rewrite Hk.
   unfold Even.
   exists (S k).
   simpl.
   rewrite <- (add_comm (k + 0)).
   rewrite <- plus_n_O.
   rewrite <- plus_Sn_m.
   rewrite <- add_comm.
   reflexivity.
Qed.

Check ev_double.

Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Proof.
  intros n. split.
  - (* -> *) apply ev_Even.
  - (* <- *) unfold Even. intros [k Hk]. rewrite Hk.
  simpl.
  rewrite <- plus_n_O.
  apply ev_double.
Qed.


Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
 intros n m E1 E2.
 induction E1 as [|n' E' IH].
 - apply E2.
 - simpl.
   apply ev_SS.
   apply IH.
Qed.

(*
 ev_SS : forall n : nat, ev n -> ev (S (S n))
 plus_Sn_m: forall n m : nat, S n + m = S (n + m)
*)
Check plus_Sn_m.

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
 intros n m E1 E2.
 induction E2 as [|n' E1' IHn'].
 - apply E1.
 - rewrite add_comm in IHn'.
   apply  ev_SS  in IHn'.
   inversion IHn' as [|n H1 H2].
   apply H1.
   inversion E1.
   rewrite add_comm in H0.
   apply H0.
Qed.

(* 
  ev_sum: forall n m : nat, ev n -> ev m -> ev (n + m)
*)
Check ev_sum.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
 intros n m p.
 intros H1 H2.
Admitted.

Check le.
(* 
  Inductive parent_of : Person -> Person -> Prop :=
    po_SC : parent_of Sage Cleo
  | po_SR : parent_of Sage Ridley
  | po_CM : parent_of Cleo Moss.
*)
Inductive total_relation : nat -> nat -> Prop :=
 total_rel n m: total_relation n m.

Theorem total_relation_is_total : forall n m, total_relation n m.
Proof.
 intros n m.
 apply (total_rel n m).
Qed.                                 

Inductive empty_relation : nat -> nat -> Prop := .

Theorem empty_relation_is_empty : forall n m, not (empty_relation n m).
Proof.
 intros n m.
 unfold not.
 intros H.
 inversion H.
Qed.

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).
Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)

  where "s =~ re" := (exp_match s re).

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1]).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : not ([1; 2] =~ Char 1).
Proof.
  intros H.
  inversion H.
Qed.

Fixpoint reg_exp_of_list { T } (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Theorem app_nil_r : forall (X:Type), forall (l:list X),
  l ++ [] = l.
Proof.
  intros.
  induction l as [| h t IH].
  - reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

Lemma MStar1 : forall T s (re : reg_exp T) ,
    s =~ re ->  s =~ Star re.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply MStarApp.
  - apply H.
  - apply MStar0.
Qed.

Lemma empty_is_empty : forall T (s : list T),
  not (s =~ EmptySet).
Proof.
 intros.
 unfold not.
 intros H.
 inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros.
  destruct H.
  apply MUnionL. apply H.
  apply MUnionR. apply H.
Qed.

Fixpoint fold {X Y: Type} (f : X->Y->Y) (l : list X) (b : Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) -> fold (@app _) ss [] =~ Star re.
Proof.
 intros.
 induction ss.
 - simpl.
   apply MStar0.
 - simpl.
   apply MStarApp.
   + apply H.
     simpl.
     left. reflexivity.
   + apply IHss.
     simpl in H.
     intros.
     apply H.
     right.
     apply H0.
Qed. 

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem ex_falso_quodlibet : forall (P: Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra. Qed.

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

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    simpl in Hin. destruct Hin.
  - (* MChar *)
    simpl. simpl in Hin.
    apply Hin.
  - (* MApp *)
    simpl.
    rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    simpl.
    rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

(* 
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).
*)
Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
match re with
| EmptySet => false
| EmptyStr => true
| Char _ => true
| App r1 r2 => re_not_empty r1 && re_not_empty r2
| Union r1 r2 =>  re_not_empty r1 || re_not_empty r2
| Star r => re_not_empty r
end.

Search " _ || _ ".

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
 intros.
 split.
 intros.
 destruct H.
 induction H.
 - reflexivity.
 - reflexivity.
 - simpl. 
   rewrite IHexp_match1.
   rewrite IHexp_match2.
   reflexivity.
 - simpl.
   rewrite IHexp_match.
   reflexivity.
 - simpl.
   rewrite IHexp_match.
   apply Bool.orb_true_r.
 - simpl.
Admitted.