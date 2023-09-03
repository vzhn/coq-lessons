Require Import Coq.Init.Nat.

Inductive LambdaTerm : Type :=
  | var (n: nat)
  | app (a: LambdaTerm) (b: LambdaTerm)
  | abst (a: LambdaTerm).

Fixpoint shift (depth: nat) (amount: nat) (t: LambdaTerm): LambdaTerm :=
  match t with
    | var v => if (depth <=? v) 
                 then var (v + amount)
                 else var v
    | app a b => app (shift depth amount a) (shift depth amount b)
    | abst a => abst (shift (depth + 1) amount a)
  end.

Fixpoint _substitution (d: nat) (t: LambdaTerm) (w: nat) (replacement: LambdaTerm): LambdaTerm := 
  match t with
    | var n => if (n =? w)
                 then shift 0 d replacement
                 else t
    | app a b => app (_substitution d a w replacement) (_substitution d b w replacement)
    | abst a => abst (_substitution (d + 1) a (w + 1) replacement)
  end.

Definition substitution (t: LambdaTerm) (replacement: LambdaTerm): LambdaTerm := 
  _substitution 0 t 0 replacement.

Fixpoint lambda_eq (a: LambdaTerm) (b: LambdaTerm): bool :=
  match a, b with
  | var n, var m => n =? m
  | app a1 b1, app a2 b2 => (lambda_eq a1 a2) && (lambda_eq b1 b2)
  | abst m, abst n => (lambda_eq m n)
  | _, _ => false
  end.

Fixpoint beta (t: LambdaTerm): LambdaTerm :=
  match t with
    | var _ => t
    | app a b => match a with
                 | abst body => substitution body b
                 | _ => let ba := beta a in
                          if (lambda_eq a ba)
                            then app a (beta b) 
                            else app ba b
                 end 
    | abst a => abst (beta a)
  end.  

Fixpoint _mk_app (n: nat) :=
 match n with
  | O => var 0
  | S n => app (var 1) (_mk_app n)
 end.

Definition nat_to_church (n: nat): LambdaTerm :=
  abst (abst (_mk_app n)).

Fixpoint _app_to_nat (t: LambdaTerm): (option nat) :=
  match t with
    | var 0 => Some 0
    | app (var 1) a => match (_app_to_nat a) with
                       | Some k => Some (S k)
                       | _ => None
                       end
    | _ => None
  end.

Definition church_to_nat (ch: LambdaTerm): (option nat) :=
  match ch with
    | (abst (abst a)) => _app_to_nat a
    | _ => None
  end.

Definition succ := 
  (abst (abst (abst (app (var 1) (app (app (var 2) (var 1)) (var 0)))))).

Example test_shift_0: shift 0 4 (var 0) = var 4.
Proof. simpl. reflexivity. Qed.

Example test_shift_1: shift 0 1 (app (var 0) (var 0)) = (app (var 1) (var 1)).
Proof. simpl. reflexivity. Qed.

Example test_shift_2: shift 0 1 (abst (abst (app (var 2) (var 1)))) = 
 (abst (abst (app (var 3) (var 1)))).
Proof. simpl. reflexivity. Qed.

Example test_shift_3: shift 0 1 (abst (abst (var 2))) = (abst (abst (var 3))).
Proof. simpl. reflexivity. Qed.

Example test_substitution_4: substitution (abst (abst (var 0))) (var 42) = (abst (abst (var 0))).
Proof. simpl. reflexivity. Qed.

Example test_substitution_5: substitution (abst (abst (var 2))) (var 42) = (abst (abst (var 44))).
Proof. simpl. reflexivity. Qed.

Example test_nat_to_church_0: nat_to_church 0 = abst (abst (var 0)).
Proof. simpl. reflexivity. Qed.

Example test_nat_to_church_1: nat_to_church 1 = abst (abst (app (var 1) (var 0))).
Proof. simpl. reflexivity. Qed.

Example test_nat_to_church_2: nat_to_church 2 = abst (abst (app (var 1) (app (var 1) (var 0)))).
Proof. simpl. reflexivity. Qed.

Example test_church_to_nat: church_to_nat (abst (abst (var 0))) = Some 0.
Proof. simpl. reflexivity. Qed.

Lemma lemma_001: forall n: nat, (_app_to_nat (_mk_app n)) = Some n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  reflexivity.
  simpl.
  rewrite IHn'.
  reflexivity.
Qed.

Lemma lemma_002:
  forall n: nat, 
   (church_to_nat (nat_to_church n)) = Some n -> 
   (church_to_nat (nat_to_church (S n))) = Some (S n).
Proof.
  simpl.
  intros.
  rewrite H.
  reflexivity.
Qed.

Theorem verify_church_conversions: 
  forall n: nat, (church_to_nat (nat_to_church n)) = Some n.
Proof.
  intros n. 
  induction n as [| n' IHn'].
  simpl. 
  reflexivity.
  apply lemma_002.
  assumption.
Qed.

Fixpoint _beta_fuel (t: LambdaTerm) (fuel: nat): (option LambdaTerm) :=
  match fuel with
  | 0 => None
  | S n => let bt := beta t in
             if (lambda_eq t bt)
               then Some t
               else _beta_fuel bt n
  end.

Definition beta_fuel (t: LambdaTerm): (option LambdaTerm) :=
  _beta_fuel t 100.

Compute (beta_fuel (app succ (nat_to_church 1))).

Compute 
 match (beta_fuel (app succ (nat_to_church 0))) with
 | Some t => church_to_nat t
 | _ => None
 end.



