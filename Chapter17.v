Require Import ZArith Lia Classical Reals Lra Classical_sets List String
               Ensembles QArith ClassicalFacts Finite_sets Powerset Finite_sets_facts Image 
               NArith DecimalString DecimalNat DecimalNat Decimal
               Fibonacci Sums Sets Binomial QRT.

Require Export Chapter16.

Import ListNotations SetNotations Choose_Notations.

Open Scope Z_scope.
Open Scope string_scope.

Definition Z_to_string (n : Z) : string :=
  NilEmpty.string_of_int (Z.to_int n).

Definition compute_quot_rem_text (pair : Z * Z) : string :=
  let (n, d) := pair in
  let q := Z.quot n d in
  let r := Z.rem n d in
  let equation := 
    Z_to_string n ++ " = " ++ Z_to_string d ++ " * " ++ Z_to_string q ++ " + " ++ Z_to_string r in
  equation.

Compute map compute_quot_rem_text [(17, 5); (17, -5); (-17, 5); (-17, -5); (256, 25); (256, -25); (-256, 25); (-256, -25)].

Close Scope string_scope.

Lemma lemma_17_2_a : forall n : Z,
  Z.Even n \/ Z.Odd n.
Proof.
  intro n. destruct (quotient_remainder_theorem_existence n 2) as [q [r [H1 H2]]]; try lia.
  assert (r = 0 \/ r = 1) as [H3 | H3] by lia; [left | right]; exists q; lia.
Qed.

Lemma lemma_17_2_b : forall n : Z,
  (Z.Even n /\ Z.Odd n) -> False.
Proof.
  intros n [[q1 H1] [q2 H2]]; lia.
Qed.

Definition find_divisors (n : nat) : list Z :=
  fold_right (fun x l => if (Z.rem (Z.of_nat n) x =? 0) then x :: l else l) [] (map Z.of_nat (seq 1 n)).

Compute find_divisors 12.
Compute find_divisors 60.

Definition in_list (x: Z) (l: list Z) : bool :=
  fold_right (fun y acc => if Z.eq_dec x y then true else acc) false l.

Notation "¬ x" := (negb x) (at level 75, right associativity).

Definition intersection (l1 l2 : list Z) : list Z :=
  fold_right (fun x l => if (in_list x l1) && (in_list x l2) && (¬in_list x l) then x :: l else l) [] l1.

Definition gcd' (n m : Z) : Z :=
  let divisors1 := find_divisors (Z.abs_nat n) in
  let divisors2 := find_divisors (Z.abs_nat m) in
  let l := intersection (divisors1) (divisors2) in
  nth (List.length l - 1) l 0.

Compute find_divisors 60.
Compute find_divisors 42.

Compute intersection (find_divisors 60) (find_divisors 42).
Compute gcd' 170 244.
Compute Z.gcd 170 244.


