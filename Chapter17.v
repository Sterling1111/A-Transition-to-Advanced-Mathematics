Require Import ZArith Lia Classical Reals Lra Classical_sets List String
               Ensembles QArith ClassicalFacts Finite_sets Powerset Finite_sets_facts Image 
               NArith DecimalString DecimalNat DecimalNat Decimal
               Fibonacci Sums Sets Binomial QRT WI_SI_WO.

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

Ltac apply_lia_to_hyps :=
  match goal with
  | H: _ |- _ => specialize (H); lia
  end.

Lemma lemma_17_2_b : forall n : Z,
  (Z.Even n /\ Z.Odd n) -> False.
Proof.
  intros n [[q1 H1] [q2 H2]].
  pose proof (quotient_remainder_theorem_uniqueness n 2 q1 q2 1 0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [_ H3].
  discriminate H3.
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

Compute (Z.rem 133 19).

Compute (map (fun p => (Z.gcd (fst p) (snd p))) [(60, 42); (667, 851); (1855, 2345); (589, 437)]).

Definition gcd_theory (a b gcd : Z) :=
  if (a =? 0) && (b =? 0) then gcd = 0 else
  (gcd | a) /\ (gcd | b) /\
  forall d, (d | a) /\ (d | b) -> d <= gcd.

Lemma gcd_satisfies_gcd_theory : forall a b, gcd_theory a b (Z.gcd a b).
Proof.
  intros a b. assert (a = 0 /\ b = 0 \/ (a <> 0 \/ b <> 0)) as [[H1 H2] | H1] by lia.
  - rewrite H1, H2. compute. reflexivity.
  - assert ((a =? 0) && (b =? 0) = false) as H3. { destruct H1 as [H1 | H1]; apply andb_false_iff; [left | right]; apply Z.eqb_neq; lia. }
    unfold gcd_theory. rewrite H3. split; [apply Z.gcd_divide_l | split; [apply Z.gcd_divide_r | intros d [H4 H5]]].
    pose proof (Z.gcd_greatest a b d H4 H5) as [k H6]. pose proof (Z.gcd_nonneg a b) as H7.
    pose proof (Z.gcd_divide_l a b) as [p H8]. pose proof (Z.gcd_divide_r a b) as [q H9].
    assert (d < 0 \/ d = 0 \/ d > 0) as [H10 | [H10 | H10]]; assert (k < 0 \/ k = 0 \/ k > 0) as [H11 | [H11 | H11]]; try nia.
Qed.

Lemma gcd_divides_both : forall a b,
  (Z.gcd a b | a) /\ (Z.gcd a b | b).
Proof.
  intros a b. split; [apply Z.gcd_divide_l | apply Z.gcd_divide_r].
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

End section_17_5.

Lemma gcd_switching : forall a b c z,
  a = z * b + c -> Z.gcd a b = Z.gcd b c.
Proof.
  intros a b c z H1. pose proof (gcd_satisfies_gcd_theory a b) as H2.
  pose proof (gcd_satisfies_gcd_theory b c) as H3.
  assert (b = 0 \/ b <> 0) as [H4 | H4] by lia.
  - rewrite H4. rewrite Z.gcd_comm. simpl. lia.
  - assert ((b =? 0) && (c =? 0) = false) as H5. { apply andb_false_iff; left; apply Z.eqb_neq; lia. }
    assert ((a =? 0) && (b =? 0) = false) as H6. { apply andb_false_iff; right; apply Z.eqb_neq; lia. }
    unfold gcd_theory in H2, H3. rewrite H6 in H2. rewrite H5 in H3.
    destruct H2 as [H2 [H7 H8]]. destruct H3 as [H3 [H9 H10]].
    assert (H11 : forall d1, (d1 | a) /\ (d1 | b) -> (d1 | c)).
    { intros d1 [H11 H12]. replace c with (a - z * b) by lia. apply Z.divide_sub_r; auto. apply Z.divide_mul_r; auto. }
    assert (H12 : forall d2, (d2 | b) /\ (d2 | c) -> (d2 | a)).
    { intros d2 [H12 H13]. rewrite H1. apply Z.divide_add_r; auto. apply Z.divide_mul_r; auto. }
    specialize (H11 (Z.gcd a b) ltac: (split; auto)). specialize (H12 (Z.gcd b c) ltac: (split; auto)).
    specialize (H10 (Z.gcd a b) ltac: (split; auto)). specialize (H8 (Z.gcd b c) ltac: (split; auto)). lia.
Qed.

Lemma lemma_17_6 : forall n : Z,
  Z.gcd (2 * n + 1) (4 * n + 3) = 1.
Proof.
  intros n. rewrite Z.gcd_comm. replace (4 * n + 3) with (2 * (2 * n + 1) + 1) by lia.
  rewrite gcd_switching with (z := 2) (c := 1); try lia. apply Z.gcd_1_r.
Qed.

Lemma lemma_17_7 : forall n : Z,
  Z.gcd (6 * n + 2) (12 * n + 6) = 2.
Proof.
  intros n. rewrite Z.gcd_comm. replace (12 * n + 6) with (2 * (6 * n + 2) + 2) by lia.
  rewrite gcd_switching with (z := 2) (c := 2); try lia. replace (6 * n + 2) with (2 * (3 * n + 1)) by lia. 
  rewrite Z.gcd_comm. apply Z.gcd_mul_diag_l; lia.
Qed.

Lemma lemma_17_8_a : forall n d : Z,
  (d >= 1) -> (n < 0) -> exists q r : Z, n = d * q + r /\ 0 <= r < d.
Proof.
  intros n d H1 H2. destruct (quotient_remainder_theorem_existence (-n) d H1) as [q [r [H3 H4]]].
  pose proof classic (r = 0) as [H5 | H5]; [exists (-q), r | exists (-q - 1), (d - r)]; lia.
Qed.

Lemma lemma_17_8_b : forall n d : Z,
  (d < 0) -> exists q r : Z, n = d * q + r /\ 0 <= r < Z.abs d.
Proof.
  intros n d H1. destruct (quotient_remainder_theorem_existence n (-d) ltac:(lia)) as [q [r [H2 H3]]].
  exists (-q), r; lia.
Qed.

Theorem division_algorithm : forall n d : Z,
  d <> 0 -> exists q r : Z, n = d * q + r /\ 0 <= r < Z.abs d.
Proof.
  intros n d H1. assert (Z.abs d = d \/ Z.abs d = -d) as [H2 | H2] by lia;
  [rewrite H2; apply quotient_remainder_theorem_existence | apply lemma_17_8_b]; lia.
Qed.