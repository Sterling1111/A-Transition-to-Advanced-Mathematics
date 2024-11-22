Require Import Imports.

Open Scope R_scope.

Ltac break_INR :=
  repeat match goal with
  | [ |- context[INR (?n + ?m)] ] =>
      rewrite plus_INR
  | [ |- context[INR (?n * ?m)] ] =>
      rewrite mult_INR
  | [ |- context[INR (S ?n)] ] =>
      rewrite S_INR
  | [ |- context[INR (?n - ?m)] ] =>
      rewrite minus_INR
  | [ |- context[INR (?n ^ ?m)] ] =>
      rewrite pow_INR
  end.

Ltac break_INR_simpl :=
  break_INR; simpl; try field_simplify; try nra; try nia.

Ltac convert_nat_to_INR_in_H :=
  try
  match goal with
  | [ H: (?x > ?y)%nat |- _ ] => apply lt_INR in H; simpl in H
  | [ H: (?x < ?y)%nat |- _ ] => apply lt_INR in H; simpl in H
  | [ H: (?x >= ?y)%nat |- _ ] => apply le_INR in H; simpl in H
  | [ H: (?x <= ?y)%nat |- _ ] => apply le_INR in H; simpl in H
  | [ H: (?x = ?y)%nat |- _ ] => apply INR_eq in H; simpl in H
  end.

Ltac solve_INR :=
  convert_nat_to_INR_in_H; try field_simplify_eq; try break_INR; simpl; try field; try nra; try lia.

Ltac solve_abs := 
  try intros; repeat unfold Rabs in *; repeat destruct Rcase_abs in *; try nra; try field; try nia.

Ltac solve_max := 
  try intros; repeat unfold Rmax in *; repeat destruct Rle_dec in *; repeat unfold Nat.max; repeat destruct le_dec; try nra; try field; try nia.

Ltac solve_min :=
  try intros; repeat unfold Rmin in *; repeat destruct Rle_dec in *; repeat unfold Nat.min; repeat destruct le_dec; try nra; try field; try nia.

Ltac solve_R :=
  try solve_INR; try solve_abs; try solve_max; try solve_min.

Lemma pow2_gt_0 : forall r, r <> 0 -> r ^ 2 > 0.
Proof.
  intros r H1. pose proof Rtotal_order r 0 as [H2 | [H2 | H2]]; try nra.
Qed.

Lemma Rmult_le_ge_reg_neg_l :
  forall r r1 r2, r * r1 >= r * r2 -> r < 0 -> r1 <= r2.
Proof. intros; nra. Qed.

Lemma Rmult_ge_le_reg_neg_l :
  forall r r1 r2, r * r1 <= r * r2 -> r < 0 -> r1 >= r2.
Proof. intros; nra. Qed.

Lemma Rabs_triang_3 : forall r1 r2 r3 : R,
  Rabs (r1 + r2 + r3) <= Rabs r1 + Rabs r2 + Rabs r3.
Proof.
  solve_abs.
Qed.

Lemma n_lt_pow2_n : forall n, INR n < 2 ^ n.
Proof.
  induction n as [| k IH].
  - simpl. lra.
  - solve_INR. assert (1 <= 2 ^ k).
    { clear; induction k; simpl; lra. } solve_INR.
Qed.

Lemma Rpow_gt_0 : forall k r,
  r > 0 -> r ^ k > 0.
Proof.
  intros k r H1. induction k as [| k' IH].
  - simpl. lra.
  - simpl. nra.
Qed.

Lemma Rpow_lt_1 : forall r n,
  0 < r < 1 -> (n > 0)%nat -> r ^ n < 1.
Proof.
  intros r n [H1 H2] H3. induction n as [| k IH].
  - lia.
  - simpl. destruct k.
    -- simpl. lra.
    -- assert (r ^ S k < 1) by (apply IH; lia). nra.
Qed.

Lemma Rpow_gt_1 : forall r n,
  r > 1 -> (n > 0)%nat -> r ^ n > 1.
Proof.
  intros r n H1 H2. induction n as [| k IH].
  - lia.
  - simpl. destruct k.
    -- simpl. lra.
    -- assert (r ^ S k > 1) by (apply IH; lia). nra.
Qed.

Lemma Rdiv_pow_distr : forall r1 r2 n,
  r2 > 0 -> (r1 / r2) ^ n = r1 ^ n / r2 ^ n.
Proof.
  intros r1 r2 n H1. induction n as [| k IH].
  - simpl. lra.
  - simpl. rewrite IH. field. pose proof Rpow_gt_0 k r2 as H2; nra.
Qed.

Lemma Rdiv_lt_1: forall a b : R, a < b -> b > 0 -> a / b < 1.
Proof.
  intros a b H1 H2.
  apply Rmult_lt_compat_r with (r := 1/b) in H1.
  - replace (a * (1 / b)) with (a / b) in H1 by lra.
    replace (b * (1 / b)) with 1 in H1 by (field; lra).
    apply H1.
  - apply Rdiv_pos_pos. lra. apply H2.
Qed.  