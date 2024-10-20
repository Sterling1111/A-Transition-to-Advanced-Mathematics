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

Definition find_divisors_pos (n : nat) : list Z :=
  fold_right (fun x l => if (Z.rem (Z.of_nat n) x =? 0) then x :: l else l) [] (map Z.of_nat (seq 1 n)).

Definition find_divisors_neg (n : nat) : list Z :=
  List.rev (map (fun x => -x) (find_divisors_pos n)).

Definition find_divisors (n : nat) : list Z :=
  find_divisors_neg n ++ find_divisors_pos n.
  
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

Lemma gcd_existence : forall a b, gcd_theory a b (Z.gcd a b).
Proof.
  intros a b.
  assert (a = 0 /\ b = 0 \/ (a <> 0 \/ b <> 0)) as [[H1 H2] | H1] by lia.
  - rewrite H1, H2. unfold gcd_theory. simpl. lia.
  - unfold gcd_theory. assert ((a =? 0) && (b =? 0) = false) as H2.
    { destruct (a =? 0) eqn:Ha; destruct (b =? 0) eqn:Hb; simpl; lia. } rewrite H2.
    split; [apply Z.gcd_divide_l | split; [apply Z.gcd_divide_r |]].
    intros d [H3 H4]. pose proof (Z.gcd_greatest a b d H3 H4) as [k H5].
    pose proof (Z.gcd_nonneg a b) as H6. assert (d < 0 \/ d = 0 \/ d > 0) as [H7 | [H7 | H7]];
    assert (k < 0 \/ k = 0 \/ k > 0) as [H8 | [H8 | H8]]; try nia.
    rewrite H8 in H5. simpl in H5. pose proof (Z.gcd_divide_r a b) as [p H9].
    pose proof (Z.gcd_divide_l a b) as [q H10]. lia.
Qed.

Lemma doggooos : forall n m : Z,
  Z.gcd n (m + n) = Z.gcd n m.
Proof.
  intros n m. pose proof (gcd_existence n (m + n)) as H1. unfold gcd_theory in H1.
  assert (n = 0 /\ (m + n) = 0 \/ (n <> 0 \/ (m + n) <> 0)) as [[H2 H3] | H2] by lia.
  - rewrite H3, H2. simpl. lia.
  - assert ((n =? 0) && ((m + n) =? 0) = false) as H3.
    { destruct (n =? 0) eqn:H4; destruct ((m + n) =? 0) eqn:H5; simpl; lia. } rewrite H3 in H1. clear H3.
    destruct H1 as [[p H3] [[q H4] H5]]. 
Admitted.

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

Require Import FunctionalExtensionality.
Check Surjective.