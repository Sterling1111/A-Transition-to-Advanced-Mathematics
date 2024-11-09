Require Import Imports Reals_util.

Open Scope R_scope.

Notation "| x |" := (Rabs x) (at level 70, format "| x |").

Definition sequence := nat -> R.

Definition arithmetic_sequence (a : sequence) (c d : R) : Prop :=
  a 0%nat = c /\ forall n : nat, a (S n) - a n = d.

Definition geometric_sequence (a : sequence) (c r : R) : Prop :=
  a 0%nat = c /\ forall n : nat, a (S n) = r * a n.

Definition limit_of_sequence (a : sequence) (L : R) : Prop :=
  forall ε : R, ε > 0 ->
    exists N : R, forall n : nat, INR n > N -> |a n - L| < ε.

Definition convergent_sequence (a : sequence) : Prop :=
  exists (L : R), limit_of_sequence a L.

Definition divergent_sequence (a : sequence) : Prop :=
  ~ convergent_sequence a.

Lemma Rinv_lt_0 : forall r, 
  / r < 0 -> r < 0.
Proof.
  intros r H1. pose proof (Rtotal_order r 0) as [H2 | [H2 | H2]]; try lra.
  - rewrite H2 in H1. rewrite Rinv_0 in H1. lra.
  - apply Rinv_0_lt_compat in H2. lra.  
Qed.

Lemma Rinv_gt_0 : forall r,
  / r > 0 -> r > 0.
Proof.
  intros r H1. pose proof (Rtotal_order r 0) as [H2 | [H2 | H2]]; try lra.
  - apply Rinv_0_lt_compat in H1. rewrite Rinv_inv in H1. lra.
  - rewrite H2 in H1. rewrite Rinv_0 in H1. lra.
Qed.

Theorem theorem_34_12 : limit_of_sequence (fun n => 1 / INR n) 0.
Proof.
  intros ε H1. exists (/ ε). intros n H2. assert (/ ε > 0) as H3 by (apply Rinv_pos; auto).
  rewrite Rminus_0_r. unfold Rabs. destruct (Rcase_abs (1 / INR n)) as [H4 | H4].
  - assert (H5 : / - INR n > 0). { apply Rinv_pos. rewrite Rdiv_1_l in H4. apply Rinv_lt_0 in H4. lra. }
    assert (H6 : INR n <> 0). { assert (INR n > 0). { rewrite Rdiv_1_l in H4. apply Rinv_lt_0 in H4. lra. } lra. }
    apply Rmult_gt_compat_r with (r := ε) in H2; try lra.
    apply Rmult_gt_compat_r with (r := / - INR n) in H2; try lra.
    rewrite Rinv_opp in H2. field_simplify in H2; nra.
  - assert (H5 : / INR n > 0). { apply Rinv_pos. rewrite Rdiv_1_l in H4. nra. }
    assert (H6 : INR n <> 0). { nra. }
    apply Rmult_gt_compat_r with (r := ε) in H2; try lra.
    apply Rmult_gt_compat_r with (r := / INR n) in H2; try lra.
    field_simplify in H2; try nra. 
Qed.

Proposition proposition_34_13 : limit_of_sequence (fun n => 1 - 3 / INR n) 1.
Proof.
  intros ε H1. exists (3 / ε). intros n H2.
  replace (1 - 3 / INR n - 1) with (- 3 / INR n) by lra.
  assert (H3 : 3 / ε > 0) by (apply Rdiv_lt_0_compat; lra).
  assert (H4 : INR n > 0) by nra. assert (H5 : -3 / INR n < 0).
  { apply Rdiv_neg_pos; nra. } 
  unfold Rabs. destruct (Rcase_abs (- 3 / INR n)) as [H6 | H6]; try nra.
  field_simplify; try lra.
  apply Rmult_gt_compat_r with (r := ε) in H2; try lra.
  apply Rmult_gt_compat_r with (r := / 3 * / INR n) in H2; try lra.
  field_simplify in H2; try lra.
Qed.

Lemma Odd_not_even : forall n, Nat.Odd n -> Nat.even n = false.
Proof.
  intros n [k H1]. rewrite H1. apply Nat.even_odd.
Qed.

Proposition proposition_34_15 : limit_of_sequence (fun n => if Nat.even n then 0 else 1 / INR n) 0.
Proof.
  intros ε H1. pose proof theorem_34_12 ε H1 as [N H2]. exists N. intros n H3.
  pose proof Nat.Even_or_Odd n as [H4 | H4].
  - apply Nat.even_spec in H4. rewrite H4. rewrite Rminus_0_r. rewrite Rabs_R0. lra.
  - apply Odd_not_even in H4. rewrite H4. auto.
Qed.

Proposition proposition_34_16 : divergent_sequence (fun n => (-1) ^ n).
Proof.
  intros [L H1]. specialize (H1 (1/2) ltac:(lra)) as [N H1].
  pose proof INR_unbounded N as [n H2]. assert (0 <= INR n) as H3.
  { replace 0 with (INR 0) by auto. apply le_INR. lia. }
  assert (L >= 0 \/ L < 0) as [H4 | H4] by lra.
  - specialize (H1 (S (2 * n)) ltac:(solve_INR)). rewrite pow_1_odd in H1.
    apply Rabs_def2 in H1 as [_ H1]. lra.
  - specialize (H1 (2 * n)%nat ltac:(solve_INR)). rewrite pow_1_even in H1.
    apply Rabs_def2 in H1 as [H1 _]. lra.
Qed.

Lemma Rmax_Rgt : forall x y z, z > Rmax x y -> z > x /\ z > y.
Proof.
  intros x y z H1. unfold Rmax in H1. destruct (Rle_dec x y); lra.
Qed.

Proposition Proposition_34_19 : limit_of_sequence (fun n => INR (n + 3) / INR (2 * n - 21)) (1/2).
Proof.
  intros ε H1. set (N := Rmax (21/2) ((27 + 42 * ε) / (4 * ε))). exists N.
  intros n H2. apply Rmax_Rgt in H2 as [H2 H3].
  assert (INR (n + 3) / INR (2 * n - 21) - 1/2 = 27 / INR (4 * n - 42)) as H4.
  { solve_INR; assert (n > 10)%nat by (apply INR_lt; simpl; lra); try lia. } rewrite H4.
  assert (INR (4 * n - 42) > 0) as H5 by (solve_INR; assert (n > 10)%nat by (apply INR_lt; simpl; lra); try lia).
  unfold Rabs. destruct (Rcase_abs (27 / INR (4 * n - 42))) as [H6 | H6].
  - pose proof Rdiv_pos_pos 27 (INR (4 * n - 42)) ltac:(lra) as H7. nra.
  - assert (INR (4 * n - 42) > 27 / ε) as H7.
    {
       solve_INR. rewrite Rplus_0_l. field_simplify; try lra. apply Rmult_gt_compat_r with (r := 4) in H3; try lra.
       field_simplify in H3; try lra. replace ((42 * ε + 27) / ε) with (27 / ε + 42) in H3 by (field; lra); lra.
       assert (n > 10)%nat by (apply INR_lt; simpl; lra); try lia.
    }
    apply Rmult_gt_compat_r with (r := ε) in H7; try lra.
    apply Rmult_gt_compat_r with (r := /INR (4 * n - 42)) in H7; try lra. field_simplify in H7; try lra. apply Rinv_pos; lra.
Qed.