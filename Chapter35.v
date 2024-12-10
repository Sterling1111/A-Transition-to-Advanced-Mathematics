Require Import Imports Sequence Series Sums Reals_util WI_SI_WO.
Require Export Chapter34.

Section section_35_1.
  Let a : sequence := (fun n => INR n).

  Example example_35_1_1 : map (partial_sum a) (seq 0 7) = [0; 1; 3; 6; 10; 15; 21].
  Proof. auto_list. Qed.

  Lemma lemma_35_1 : forall n,
    partial_sum a n = (INR n * (INR n + 1)) / 2.
  Proof.
    intros n. unfold partial_sum, a. rewrite proposition_13_5. reflexivity.
  Qed.
End section_35_1.

Section section_35_2.
  Variable (a : sequence) (c d : R).
  Hypothesis H1 : arithmetic_sequence a c d.

  Example example_35_2_1 : map (partial_sum a) (seq 0 4) = [c; 2 * c + d; 3 * c + 3 * d; 4 * c + 6 * d].
  Proof. rewrite H1. auto_list. Qed.
  
  Lemma lemma_35_2 : forall n,
    partial_sum a n = c * (INR n + 1) + d * (INR n * (INR n + 1)) / 2.
  Proof.
    unfold partial_sum. rewrite H1. intro n. induction n as [| k IH].
    - sum_simpl. lra.
    - rewrite sum_f_i_Sn_f; try lia. rewrite IH. solve_INR.
  Qed.

  Lemma lemma_35_2' : forall n,
    partial_sum a n = c * (INR n + 1) + d * (INR n * (INR n + 1)) / 2.
  Proof.
    intros n. unfold partial_sum. rewrite H1. rewrite <- sum_f_plus; try lia.
    rewrite <- r_mult_sum_f_i_n_f_l. rewrite sum_f_const. rewrite proposition_13_5.
    rewrite Nat.sub_0_r. solve_INR.
  Qed.
End section_35_2.

Section section_35_3.
  Let a : sequence := (fun n => 1 / 2 ^ n).

  Lemma lemma_35_3_a : forall n, partial_sum a n = (2 - 1 / 2 ^ n).
  Proof.
    apply nth_term_in_series_sequence_35_5.
  Qed.

  Lemma lemma_35_3_b : ∑ 0 ∞ a = 2.
  Proof.
    unfold series_sum. 
    set (b := (fun n => 1 / INR n)). set (c := (fun n : nat => 2)).
    assert (⟦ lim_s ⟧ a = 0) as H1.
    {
      apply (sequence_squeeze_lower b a 0).
      - apply theorem_34_12.
      - exists 0. intros n H1. unfold a, b. assert (INR n < 2 ^ n) as H2 by apply n_lt_pow2_n. apply Rle_ge.
        apply Rmult_le_reg_r with (r := INR n); try nra; apply Rmult_le_reg_r with (r := 2^n); try nra; field_simplify; try nra.
      - intro n. apply Rlt_le. apply Rdiv_pos_pos; try lra. apply Rpow_gt_0; lra.
    }
    assert (⟦ lim_s ⟧ c = 2) as H2. { apply limit_of_const_sequence. }
    replace (partial_sum a) with (fun n => 2 - 1 / 2 ^ n). 2 : { apply functional_extensionality. intro n. rewrite lemma_35_3_a; auto. }
    replace 2 with (2 - 0) at 1 by lra. apply limit_of_sequence_sub; auto.
  Qed.

  Lemma lemma_35_3_b' : ∑ 0 ∞ a = 2.
  Proof.
    unfold series_sum. intros ε H1. pose proof theorem_34_12 ε H1 as [N H2]. exists N. intros n H3.
    specialize (H2 n H3). rewrite lemma_35_3_a. replace (2 - 1 / 2 ^ n - 2) with (- 1 / 2 ^ n) by lra.
    admit.
  Admitted.
End section_35_3.

Section section_35_4.
  Let a : sequence := (fun n => 1 / 3^n).

  Lemma lemma_35_4 : convergent_sequence (partial_sum a).
  Proof.
    apply Monotonic_Sequence_Theorem_Increasing.
    - intros n. unfold partial_sum, a. rewrite sum_f_i_Sn_f; try lia. pose proof pow_le (1/3) (S n) ltac:(lra) as H1.
      replace ((1 / 3) ^ S n) with (1 / 3^(S n)) in H1. 2 : { rewrite Rdiv_pow_distr; try lra. rewrite pow1. lra. } lra.
    - set (b := partial_sum (fun n => 1 / 2 ^ n)). assert (bounded_above b) as H1.
      { apply convergent_bounded. exists 2. apply lemma_35_3_b. }
      apply bounded_above_by_bound_above_sequence with (b := b); auto. intros n. unfold b, partial_sum, a.
      apply sum_f_congruence_le; try lia. intros k H2. assert (0 < 3^k /\ 0 < 2^k) as [H3 H4] by (split; apply Rpow_gt_0; lra).
      apply Rmult_le_reg_r with (r := 3 ^ k); try lra; apply Rmult_le_reg_r with (r := 2 ^ k); field_simplify; try lra.
      apply pow_incr; lra.
  Qed.
End section_35_4.

Section section_35_5.
  Let a : sequence := (fun n => 1 / (INR n + 1)). 

  Let f1 : nat -> nat := (fun n => match n with 0%nat => 0%nat | S n' => (2 ^ n')%nat end).
  Let f2 : nat -> nat := (fun n => (2^n - 1)%nat).

  Let t : sequence := (fun n => sum_f (f1 n) (f2 n) a).

  Example partial_sum_a_0 : partial_sum a 0 = 1.
  Proof.
    compute; lra.
  Qed.

  Example test_t : map t (seq 0 4) = [ 1;   1/2;    1/3 + 1/4;    1/5 + 1/6 + 1/7 + 1/8 ].
  Proof. auto_list. Qed.

  Example test_partial_sum_a : map (partial_sum a) (map f2 (seq 0 4)) = 
    [t 0%nat; partial_sum a (f2 0) + t 1%nat; partial_sum a (f2 1) + t 2%nat; partial_sum a (f2 2) + t 3%nat].
  Proof. auto_list. Qed.

  (* partial_sum a (f2 0) = t 0                       *)
  (* partial_sum a (f2 1) = partial_sum a (f2 0) + t 1*)
  (* partial_sum a (f2 2) = partial_sum a (f2 1) + t 2*)
  (* partial_sum a (f2 3) = partial_sum a (f2 2) + t 3*)
  (* ................................................ *)
  (*                       .                          *)
  (*                       .                          *)
  (*                       .                          *)
  (* ................................................ *)
  (* partial_sum a (f2 0) = t 0 and                   *)
  (* partial_sum a (f2 (S n)) = partial_sum a (f2 n) + t (S n)*)
  (* this should make for an easy induction later on*)

  Open Scope nat_scope.
  
  Lemma f1_le_f2 : forall n, 
    f1 n <= f2 n.
  Proof.
    intros n. unfold f1, f2. destruct n as [| n]; simpl; lia.
  Qed.

  Lemma pow2_gt_0 : forall n,
    2 ^ n > 0.
  Proof.
    intros n. induction n as [| k IH]; simpl; lia.
  Qed.

  Lemma f1_n_eq_f2_n_minus_1 : forall n,
    f1 (S n) = S (f2 n).
  Proof.
    intros n. unfold f1, f2. destruct n as [| n]; try lia. simpl. lia.
    pose proof pow2_gt_0 (S n) as H2. lia.
  Qed.

  Lemma S_f2 : forall n,
    f2 (S n) = S (2 * (f2 n)).
  Proof.
    intros n. unfold f2. simpl. pose proof pow2_gt_0 n as H1. lia.
  Qed.

  Close Scope nat_scope.
  Open Scope R_scope.

  Lemma a_decreasing : decreasing a.
  Proof.
    intros n. unfold a. apply Rle_ge. pose proof pos_INR n as H1.
    apply Rmult_le_reg_l with (r := INR n + 1); try lra. apply Rmult_le_reg_l with (r := INR (S n) + 1);
    field_simplify; solve_INR.
  Qed.

  Lemma lemma_35_5_a : forall n, t n >= 1/2.
  Proof.
    intros n. assert (t n >= INR (f2 n - f1 n + 1) * a (f2 n)) as H1.
    { apply sum_f_ge; [ apply f1_le_f2 | apply a_decreasing ]. }
    unfold f1, f2, a in H1. destruct n.
    - compute; lra.
    - replace (INR (2 ^ S n - 1 - 2 ^ n + 1)) with (INR (2^n)) in H1.
      2 : { solve_INR. rewrite Nat.add_0_r. pose proof Rpow_gt_0 n 2 ltac:(lra) as H2. replace 2 with (INR 2) in H2 by auto.
            rewrite <- pow_INR in H2. replace 0 with (INR 0) in H2 by auto. apply INR_lt in H2. nia. }
      replace (INR (2 ^ S n - 1) + 1) with (2 * 2 ^ n) in H1.
      2 : { solve_INR. 2 : { pose proof pow2_gt_0 n as H2. nia. } field_simplify. replace (0 + 1 + 1) with 2 by lra. nra. }
      rewrite pow_INR in H1. replace (INR 2) with 2 in H1 by auto. field_simplify in H1. nra. apply pow_nonzero; lra.
  Qed.

  Lemma lemma_35_5_b' : forall n,
    partial_sum a (f2 (S n)) = partial_sum a (f2 n) + t (S n).
  Proof.
    induction n as [| k IH].
    - compute; lra.
    - assert (k = 0 \/ k > 0)%nat as [H1 | H1] by lia; subst; try (compute; lra).
      assert (f2 k > 0)%nat as H2. { unfold f2. destruct k; simpl. lia. pose proof pow2_gt_0 k as H2. lia. }
      rewrite IH. unfold partial_sum, t. repeat rewrite f1_n_eq_f2_n_minus_1. repeat rewrite <- sum_f_combine; try lra.
      -- repeat rewrite S_f2. nia.
      -- rewrite S_f2. nia.
  Qed.

  Lemma lemma_35_5_b : forall n,
    partial_sum a (f2 n) >= 1 + INR n / 2.
  Proof.
    induction n as [| k IH].
    - compute; lra.
    - assert (k = 0 \/ k > 0)%nat as [H1 | H1] by lia; subst; try (compute; lra).
      rewrite lemma_35_5_b'. assert (t (S k) >= 1/2) as H2 by apply lemma_35_5_a.
      solve_INR.
  Qed.

  Lemma lemma_35_c : divergent_sequence (partial_sum a).
  Proof.
    intros L. exists 1. split; try lra. intros N. pose proof INR_unbounded (Rmax N L) as [n H1].
    exists (f2 (2 * n)). split.
    - unfold f2. assert (2 ^ (2 * n) - 1 >= n)%nat as H2.
      {
        clear. induction n as [| k IH].
        - simpl. lia.
        - simpl. repeat rewrite Nat.add_0_r. replace (k + S k)%nat with (S (2 * k)) by lia.
          simpl. repeat rewrite Nat.add_0_r. replace (k + k)%nat with (2 * k)%nat by lia.
          pose proof pow2_gt_0 (2 * k) as H3. lia. 
      }
      apply le_INR in H2. assert (INR n > N) as H3 by solve_max. lra.
    - pose proof lemma_35_5_b (2 *n) as H2.
      replace (1 + INR (2 * n) / 2) with (1 + INR n) in H2 by solve_INR.
      assert (INR n > L) as H3 by solve_max. solve_abs.
  Qed.

End section_35_5.