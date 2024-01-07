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

End MumbleGrumble.

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

Definition snd {X Y: Type} (p: X * Y): Y :=
match p with
| (x, y) => y
end.

Fixpoint combine {X Y: Type} (lx: list X) (ly: list Y) : list (X * Y) :=
match lx, ly with
| [], _ => []
| _, [] => []
| x::tx, y::ty => (x, y) :: (combine tx ty)
end.

Fixpoint split {X Y: Type} (l: list (X*Y)): (list X) * (list Y) :=
match l with
| [] => ([], [])
| (x, y) :: tl => ( x :: fst (split tl), y :: snd (split tl))
end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. simpl. reflexivity. Qed.


Module OptionPlayground.
Inductive option (X: Type): Type :=
| Some (x: X)
| None.

Arguments Some {X}.
Arguments None {X}.
End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : OptionPlayground.option X :=
  match l with
  | nil => OptionPlayground.None
  | a :: l' => match n with
               | O => OptionPlayground.Some a
               | S n' => nth_error l' n'
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = OptionPlayground.Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = OptionPlayground.Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = OptionPlayground.None.
Proof. reflexivity. Qed.

Definition doit3times {X: Type} (f: X -> X) (n: X): X :=
 f (f (f n)).

Check @doit3times: forall X: Type, (X -> X) -> X -> X.

Fixpoint filter {X: Type} (test: X -> bool) (l: list X): list X :=
match l with
| [] => []
| h :: t => if test h then h :: (filter test t)
            else filter test t
end.

Fixpoint even (n: nat): bool :=
match n with
| 0 => true
| S n' => negb (even n')
end.

Example test_filter1: filter even [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Example test_anon_fun':
 doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Require Import Arith.
Require Import Coq.Init.Nat.
Require Import Coq.Init.Peano.

Example test_filter2':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l: list nat): list nat :=
  filter (fun l => ((andb (leb 7 l) (even l)))) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Fixpoint partition {X: Type}
                     (test: X -> bool)
                     (l: list X)
                    : list X * list X :=
match l with
| [] => ([], [])
| hd::tl => let (pleft, pright) := partition test tl in
             if test hd
              then (hd::pleft, pright)
              else (pleft, hd::pright)
end.

Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y: Type} (f: X -> Y) (l: list X): list Y :=
match l with
| [] => []
| h::t => (f h) :: (map f t)
end.

Lemma map_distrib: forall (X Y: Type) (f: X -> Y) (a b: list X),
map f (a ++ b) = (map f a) ++ (map f b).
Proof.
intros.
induction a as [| lh' lt' IHlt'].
- reflexivity.
- simpl. rewrite IHlt'. reflexivity.
Qed.


Theorem map_rev: forall (X Y: Type) (f: X -> Y) (l: list X),
map f (rev l) = rev (map f l).
Proof.
intros x y f l.
induction l as [|lh' lt' IHlt'].
- reflexivity.
- simpl. rewrite map_distrib. rewrite IHlt'. reflexivity.   
Qed.

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X): list Y :=
match l with
| [] => []
| hd :: tl => (f hd) ++ flat_map f tl
end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Definition option_map {X Y: Type} (f: X -> Y) (xo: option X): option Y :=
match xo with
| None => None
| Some x => Some (f x)
end.

Fixpoint fold {X Y: Type} (f: X -> Y -> Y) (l: list X) (b: Y): Y :=
match l with
| nil => b
| h::t => f h (fold f t b)
end.

Definition constfun {X: Type} (x: X): nat -> X :=
 fun (k: nat) => x.

Definition ftrue := constfun true.

Check plus.

Definition fold_length {X: Type} (l: list X): nat :=
 fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct: forall X (l: list X),
 fold_length l = length l.
Proof.
intros.
induction l as [| lh' lt' IHlt'].
- reflexivity.
- simpl. rewrite <- IHlt'. reflexivity.
Qed.

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X): list Y :=
fold (
 fun (x: X) (r: list Y) => 
  [f x] ++ r
) l [].


Lemma fold_map_empty: forall {X Y: Type} (f: X -> Y) (X: Type),
 fold_map f [ ] = [ ].
Proof.
 - intros. 
 destruct fold_map eqn:fold_hyp.
 + reflexivity.
 + discriminate.
Qed.

Lemma app_empty: forall (X: Type) (l: list X),
l ++ [ ] = l.
Proof.
 induction l as [| lh ltl IHl].
 - reflexivity.
 - simpl. rewrite IHl. reflexivity.
Qed.
 

Lemma fold_map_same: forall (X Y: Type) (f: X -> Y) (a: X) (b: X) (l: list X),
fold_map f (a::l) = fold_map f [a] ++ fold_map f l /\ a = b-> 
fold_map f (b::l) = fold_map f [b] ++ fold_map f l.
Proof.
 intros.
 destruct H.
 rewrite <- H0.
 rewrite <- H. 
 reflexivity.
Qed.

Theorem fold_map_is_correct: forall X Y (f: X -> Y) (l: list X),
 fold_map f l = map f l.
Proof.
 intros.
 induction l as [| lh' lt' IHt'].
 - reflexivity.
 - simpl. rewrite <- IHt'.
   reflexivity.
Qed.

Definition prod_curry {X Y Z: Type}
(f: X * Y -> Z) (x: X) (y: Y): Z := f (x, y).

Definition prod_uncurry {X Y Z: Type}
(f: X -> Y -> Z) (p: X * Y): Z :=
 f (fst p) (snd p).


Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry: forall (X Y Z: Type)
                              (f: X -> Y -> Z)
                              x y,
 prod_curry (prod_uncurry f) x y = f x y.
Proof.
 intros.
 unfold prod_curry.
 unfold prod_uncurry.
 reflexivity.
Qed.

Module Church.
Definition cnat := forall X: Type, (X -> X) -> X -> X.
Definition zero: cnat := fun (X: Type) (f: X -> X) (x: X) => x.
Definition one: cnat := fun (X: Type) (f: X -> X) (x: X) => f x.
Definition two: cnat := fun (X: Type) (f: X -> X) (x: X) => f (f x).
Definition three : cnat := @doit3times.
Definition zero' : cnat := fun (X: Type) (succ: X -> X) (zero: X) => zero.

Definition scc (n: cnat): cnat := fun (X: Type) (f: X -> X) (x: X) => f (n X f x).


Example scc_1 : scc zero = one.
Proof. simpl. reflexivity. Qed.
Example scc_2 : scc one = two.
Proof. reflexivity. Qed.
Example scc_3 : scc two = three.
Proof. reflexivity. Qed.

Definition plus (n m: cnat): cnat :=
 fun (X: Type) (f: X -> X) (x: X) => m X f (n X f x).

Example plus_1 : plus zero one = one.
Proof. simpl. reflexivity. Qed.

Example plus_2 : plus two three = plus three two.
Proof. simpl. reflexivity. Qed.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. simpl. reflexivity. Qed.

Definition mult (n m: cnat): cnat :=
 fun (X: Type) (f: X -> X) (x: X) => m X (n X f) x.

Example mult_1 : mult one one = one.
Proof. simpl. reflexivity. Qed.

Example mult_2 : mult zero (plus three three) = zero.
Proof. simpl. reflexivity. Qed.

Example mult_3 : mult two three = plus three three.
Proof. simpl. reflexivity. Qed.

Definition exp (n m : cnat) : cnat :=
 fun (X: Type) (f: X -> X) (x: X) => ((m (X->X)) (n X)) f x.


Compute (exp three two).

Example exp_1 : exp two two = plus two two.
Proof. simpl. reflexivity. Qed.


Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. simpl. reflexivity. Qed.


Example exp_2 : exp three zero = one.
Proof. simpl. reflexivity. Qed.
