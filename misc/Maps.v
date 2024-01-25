From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
Set Default Goal Selector "!".

Locate "+".

Check String.eqb_refl :
  forall x : string, (x =? x)%string = true.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A) (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

Check t_update.

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

Check examplemap.

Notation "'_' '!->' v" := (t_empty v) (at level 100, right associativity).
Notation "x '!->' v ';' m" := (t_update m x v) (at level 100, v at next level, right associativity).

Example example_empty := (_ !-> false).

Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _ !-> false
  ).

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  (_ !-> v) x = v.
Proof.
 intros.
 unfold t_empty.
 reflexivity.
Qed.

Search " _ =? _ ".

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof.
 intros.
 unfold t_update.
 rewrite String.eqb_refl.
 reflexivity.
Qed.

Module Props.
Module And.

Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.
Arguments conj [P] [Q].
Notation "P /\ Q" := (and P Q) : type_scope.

Print prod.
Print sum.

Theorem proj1' : forall P Q,
  P /\ Q -> P.
Proof.
  intros P Q HPQ. destruct HPQ as [HP HQ]. apply HP.
  Show Proof.
Qed.

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HQ HP]. split.
    + apply HP.
    + apply HQ.
Qed.
End And.

Module Or.
Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.
Arguments or_introl [P] [Q].
Arguments or_intror [P] [Q].
Notation "P \/ Q" := (or P Q) : type_scope.

Definition inj_l : forall (P Q : Prop), P -> P \/ Q :=
  fun P Q HP => or_introl HP.
Theorem inj_l' : forall (P Q : Prop), P -> P \/ Q.
Proof.
  intros P Q HP. left. apply HP.
Qed.
Definition or_elim : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R :=
  fun P Q R HPQ HPR HQR =>
    match HPQ with
    | or_introl HP => HPR HP
    | or_intror HQ => HQR HQ
    end.

Theorem or_elim' : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R.
Proof.
  intros P Q R HPQ HPR HQR.
  destruct HPQ as [HP | HQ].
  - apply HPR. apply HP.
  - apply HQR. apply HQ.
Qed.
End Or.

Inductive ev : nat -> Prop 
:=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Module Ex.
Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  | ex_intro : forall x : A, P x -> ex P.
Notation "'exists' x , p" :=
  (ex (fun x => p))
    (at level 200, right associativity) : type_scope.
End Ex.

Definition ex_ev_Sn : ex (fun n => ev (S n)). Admitted.

