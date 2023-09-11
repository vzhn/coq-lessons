
Definition sample (a b: nat): Prop :=
match (a, b) with
| (0, 1) => True
| (1, 2) => True
| (0, 2) => True
| _ => False
end.

Definition relation (T: Type) := T -> T -> Prop.

Check sample: nat -> nat -> Prop. 
Check sample: relation nat.

Definition transitive {T: Type} (R: relation T) :=
 forall a b c : T, (R a b) -> (R b c) -> (R a c).

Theorem sample_trans: transitive sample.
Proof.
 unfold transitive, sample. intros. 
  destruct a as [|[|]], b as [|[|]], c as [|[|]]; auto;
  contradiction. 
Qed.

Goal forall n: nat, n + n >= n. 
Proof.
 destruct n as [|[|[|]]].
auto.
Qed.


