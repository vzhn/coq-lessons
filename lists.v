Inductive boollist: Type :=
| bool_nil
| bool_cons (b: bool) (l: boollist).


Inductive list' (X: Type): Type :=
| nil'
| cons' (x: X) (l: list' X).

Check list.
Check nil.
Check cons.

Fixpoint repeat (X: Type) (x: X) (count: nat): list X :=
match count with
| 0 => nil
| S count' => cons  x (repeat X x count')
end.

Example test_repeat1 :
  repeat nat 4 2 = cons  4 (cons  4 (nil)).
Proof. reflexivity. Qed.

Example test_repeat2 :
  repeat bool false 1 = cons false (nil).
Proof. reflexivity. Qed.

Module MumbleGrumble.

Inductive mumble: Type :=
| a
| b (x: mumble) (y: nat)
| c.

Inductive grumble (X: Type) : Type :=
| d (m: mumble)
| e (x: X).

Fixpoint repeat'' X x count : list X :=
match count with
| 0 => nil
| S count' => cons x (repeat'' _ x count')
end.

Fail Definition mynil := nil.
Definition mynil: list nat := nil.

Check @nil : forall X : Type, list X.

Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).


Theorem app_nil_r : forall (X: Type), forall l: list X,
 l ++ [] = l.
Proof.
 intros X l.
 induction l as [| lh lt IHl].
 - reflexivity.
 - simpl. rewrite IHl.
   reflexivity.
Qed.

Theorem app_assoc: forall A (l m n: list A),
 l ++ m ++ n = (l ++ m) ++ n.
Proof.
 intros A l m n.
 induction l as [| lh lt IHl]. 
 - reflexivity.
 - simpl. rewrite IHl. reflexivity.
Qed.

Lemma app_lengh : forall (X: Type) (l1 l2: list X),
 length (l1 ++ l2) = length l1 + length l2.
Proof.
 intros X l1 l2.
 induction l1 as [| lh lt IHl].
 - reflexivity.
 - simpl. rewrite IHl. reflexivity.
Qed.

Fixpoint rev {X: Type} (l: list X): list X :=
match l with
| nil => nil
| lh :: lt => rev lt ++ [lh]
end.

Lemma list_plus_empty: forall (X: Type) (l: list X),
 l ++ [] = l.
Proof.
 intros.
 induction l.
 - reflexivity.
 - simpl.
   rewrite IHl.
 reflexivity.
Qed.

Theorem rev_app_distr: forall X (l1 l2: list X),
 rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
 intros.
 induction l1 as [| l1h l1t IHl].
 - simpl.
   rewrite list_plus_empty.
   reflexivity.
 - simpl. rewrite IHl.
   simpl. rewrite app_assoc.
   reflexivity. 
Qed.

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

Inductive prod (X Y: Type): Type :=
| pair (x: X) (y: Y).

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y): type_scope.


Definition fst {X Y: Type} (p: X * Y): X :=
match p with
| (x, y) => x
end.


