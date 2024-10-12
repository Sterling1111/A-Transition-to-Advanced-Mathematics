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

Compute (map (fun p => (Z.gcd (fst p) (snd p))) [(60, 42); (667, 851); (1855, 2345); (589, 437)]).

Definition gcd_theory (a b gcd : Z) :=
  if (a =? 0) && (b =? 0) then gcd = 0 else
  (gcd | a) /\ (gcd | b) /\
  forall d, (d | a) /\ (d | b) -> d <= gcd.

Lemma gcd_existence : forall a b, exists g, gcd_theory a b g.
Proof.
  intros a b.
  exists (Z.gcd a b).
  unfold gcd_theory.
  split; [apply Z.gcd_divide_l | split; [apply Z.gcd_divide_r |]].
  intros d [H1 H2]. pose proof (Z.gcd_greatest a b d H1 H2) as [k H3].
  pose proof (Z.gcd_nonneg a b) as H4. assert (d < 0 \/ d = 0 \/ d > 0) as [H5 | [H5 | H5]];
  assert (k < 0 \/ k = 0 \/ k > 0) as [H6 | [H6 | H6]]; try nia.
  rewrite H6 in H3. simpl in H3. rewrite H3. 
Qed.

Lemma doggooos : forall n m : nat,
  Nat.gcd n (m + n) = Nat.gcd n m.
Proof.
  intros n m. induction n as [| k IH]; [simpl; lia |].
  Locate Nat.gcd.
  About Nat.gcd.
  Search (Nat.gcd).
  Print Nat.gcd.
  pose proof (Nat.gcd_greatest).
Qed.

Section section_17_5.
  Open Scope nat_scope.
  Local Definition F := Fibonacci.fibonacci_nat.

  Lemma lemma_17_5 : forall n,
    Nat.gcd (F (S n)) (F n) = 1.
  Proof.
    intros n. induction n as [| k IH]; try reflexivity.
    rewrite fib_S_S_n_nat. rewrite Nat.gcd_comm. rewrite Nat.add_comm.
    rewrite Nat.gcd_add_diag_r. apply IH.
  Qed.

  Search Nat.gcd.
  Print Nat.gcd.

End section_17_5.

