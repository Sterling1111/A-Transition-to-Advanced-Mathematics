Require Import Imports Sums Sequence Reals_util Chapter7.

Open Scope R_scope.

Definition partial_sum (a : sequence) (n : nat) := ∑ 0 n a.

Definition series_converges (a : sequence) : Prop :=
  convergent_sequence (partial_sum a).

Definition series_diverges (a : sequence) : Prop :=
  divergent_sequence (partial_sum a).

Definition series_sum (a : sequence) (L : R) : Prop :=
  ⟦ lim_s ⟧ (partial_sum a) = L.

Notation "'∑' 0 '∞' a '=' S" := (series_sum a S)
 (at level 45, a at level 0, S at level 0,
  format "'∑'  0  '∞'  a  '='  S").

Section section_35_2.
  Let a : sequence := (fun n => 1).

  Example example_35_2_1 : partial_sum a 0 = 1.
  Proof. unfold partial_sum, a. sum_simpl. reflexivity. Qed.

  Example example_35_2_2 : partial_sum a 1 = 2.
  Proof. unfold partial_sum, a. sum_simpl. reflexivity. Qed.

  Example example_35_2_3 : partial_sum a 2 = 3.
  Proof. unfold partial_sum, a. sum_simpl. reflexivity. Qed.

  Example example_35_2_4 : partial_sum a 3 = 4.
  Proof. unfold partial_sum, a. sum_simpl. reflexivity. Qed.

  (* From this we can guess that the partial sums are equal to their ending bound + 1.
     We will now prove this by induction. *)

  Lemma nth_term_in_series_sequence_35_2 : forall n, partial_sum a n = (INR n + 1).
  Proof.
    unfold partial_sum, a. induction n as [| k IH].
    - sum_simpl. reflexivity.
    - rewrite sum_f_i_Sn_f; try lia. rewrite IH. solve_INR.
  Qed.

  Lemma sequence_of_partial_sums_diverges_35_2 : series_diverges a.
  Proof.
    intros L. exists 1; split; try lra.
    intros N. pose proof INR_unbounded (Rmax N L) as [n H1]. exists n. split. solve_max.
    rewrite nth_term_in_series_sequence_35_2. assert (INR n > L) as H2 by solve_max. solve_abs.
  Qed.
End section_35_2.

Section section_35_3.
  Let b : sequence := (fun n => 1 / (INR n + 1) - 1 / (INR n + 2)).

  Example example_35_3_b0 : (b 0%nat) = 1 / 2.
  Proof. unfold b. simpl; field_simplify. reflexivity. Qed.

  Example example_35_3_b1 : (b 1%nat) = 1 / 6.
  Proof. unfold b. simpl; field_simplify. reflexivity. Qed.

  Example example_35_3_b2 : (b 2%nat) = 1 / 12.
  Proof. unfold b. simpl; field_simplify. reflexivity. Qed.

  Example example_35_3_b3 : (b 3%nat) = 1 / 20.
  Proof. unfold b. simpl; field_simplify. reflexivity. Qed.

  Example example_35_3_s0 : partial_sum b 0 = 1 / 2.
  Proof. unfold partial_sum, b. sum_simpl. reflexivity. Qed.

  Example example_35_3_s1 : partial_sum b 1 = 2 / 3.
  Proof. unfold partial_sum, b. sum_simpl. lra. Qed.

  Example example_35_3_s2 : partial_sum b 2 = 3 / 4.
  Proof. unfold partial_sum, b. sum_simpl. lra. Qed.

  Example example_35_3_s3 : partial_sum b 3 = 4 / 5.
  Proof. unfold partial_sum, b. sum_simpl. lra. Qed.

  Example example_35_3_s4 : partial_sum b 4 = 5 / 6.
  Proof. unfold partial_sum, b. sum_simpl. lra. Qed.

  Lemma nth_term_in_series_sequence_35_3 : forall n, partial_sum b n = 1 - (1 / (INR n + 2)).
  Proof.
    unfold partial_sum, b. induction n as [| k IH].
    - sum_simpl. reflexivity.
    - rewrite sum_f_i_Sn_f; try lia. rewrite IH. assert (0 <= INR k) by (apply pos_INR). solve_INR.
  Qed.

  Lemma sequence_of_partial_sums_converges_35_3 : series_converges b.
  Proof.
    exists 1. intros ε H1. exists (1 / ε - 2). intros n H2. rewrite nth_term_in_series_sequence_35_3.
    pose proof pos_INR n as H3. assert (-1 / (INR n + 2) < 0) as H4. { apply Rdiv_neg_pos; try lra. }
    replace ((|(1 - 1 / (INR n + 2) - 1)|)) with (1 / (INR n + 2)); solve_abs.
    apply Rplus_gt_compat_r with (r := 2) in H2; apply Rmult_gt_compat_r with (r := ε) in H2;
    apply Rmult_gt_compat_r with (r := / (INR n + 2)) in H2; field_simplify in H2; try lra.
  Qed.
End section_35_3.

Lemma partial_sum_rec : forall a n,
  (n > 0)%nat -> partial_sum a n = partial_sum a (n - 1) + a n.
Proof.
  intros a n H1. unfold partial_sum. replace n%nat with (S (n - 1)) at 1 by lia.
  rewrite sum_f_i_Sn_f; try lia. replace (S (n - 1)) with n by lia. reflexivity.
Qed.

Theorem theorem_35_6 : forall a : sequence,
  series_converges a -> ⟦ lim_s ⟧ a = 0.
Proof.
  intros a [L H1] ε H2. specialize (H1 (ε / 2) ltac:(nra)) as [M H4].
  exists (Rmax 1 (M + 1)). intros n H5. apply Rmax_Rgt in H5 as [H5 H6].
  assert (INR (n - 1) > M) as H7. { solve_INR. apply INR_le. solve_INR. }
  specialize (H4 n ltac:(lra)) as H8. specialize (H4 (n - 1)%nat ltac:(auto)) as H9.
  assert (n > 0)%nat as H10. { apply INR_lt. solve_INR. } rewrite partial_sum_rec in H8; try lia.
  solve_abs.
Qed.

Theorem theorem_35_7 : forall a : sequence,
  ~ ⟦ lim_s ⟧ a = 0 -> series_diverges a.
Proof.
  intros a H1. pose proof theorem_35_6 a as H2. apply contra_2 in H2; auto.
  unfold series_diverges. apply divergent_sequence_iff. intros H3. apply H2.
  unfold series_converges. auto.
Qed.

