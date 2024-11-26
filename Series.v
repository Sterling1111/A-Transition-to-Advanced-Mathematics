Require Import Imports Sums Sequence Reals_util Chapter34 Notations.

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

  Example example_35_2_1 : map (partial_sum a) (seq 0 4) = [1; 2; 3; 4].
  Proof. auto_list. Qed.

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

  Example example_35_3_1 : map b (seq 0 4) = [1 / 2; 1 / 6; 1 / 12; 1 / 20].
  Proof. auto_list. Qed.

  Example example_35_3_2 : map (partial_sum b) (seq 0 5) = [1/2; 2/3; 3/4; 4/5; 5/6].
  Proof. auto_list. Qed.

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

Section section_35_5.
  Let a : sequence := (fun n => 1 / 2 ^ n).

  Example example_35_5_1 : map (partial_sum a) (seq 0 4) = [1; 3/2; 7/4; 15/8].
  Proof. auto_list. Qed.

  Lemma nth_term_in_series_sequence_35_5 : forall n, partial_sum a n = (2 - 1 / 2 ^ n).
  Proof.
    unfold partial_sum, a. induction n as [| k IH].
    - sum_simpl. lra.
    - rewrite sum_f_i_Sn_f; try lia. rewrite IH. assert (2^k <> 0) by (clear; induction k; simpl; lra).
      solve_INR.
  Qed.
End section_35_5.

Lemma partial_sum_rec : forall a n,
  (n > 0)%nat -> partial_sum a n = partial_sum a (n - 1) + a n.
Proof.
  intros a n H1. unfold partial_sum. replace n with (S (n - 1)) by lia.
  rewrite sum_f_i_Sn_f; try lia. replace (S (n - 1)) with n by lia. reflexivity.
Qed.

(*
  we can just use solve_abs but this is the reasoning that makes sense to people
  |an|  = |sn − sn−1|
        = |(sn − L) + (L − sn−1)|
        ≤ |sn − L| + |L − sn−1| (by the triangle inequality)
        = |sn − L| + |sn−1 − L|
        < ε/2 + ε/2
        = ε
*)
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

Example example_35_8 : series_diverges (fun n => INR (n + 3) / INR (2 * n - 21)).
Proof.
  apply theorem_35_7. intros H1. pose proof Proposition_34_19 as H2.
  assert (0 = 1/2) as H3. { apply limit_of_sequence_unique with (a := fun n => INR (n + 3) / INR (2 * n - 21)); auto. }
  lra.
Qed.

Example example_35_9 : series_diverges (fun n => (-1) ^ n).
Proof.
  apply theorem_35_7. intros H1. pose proof proposition_34_16 as H2.
  specialize (H2 0). apply not_limit_of_sequence_iff in H2. tauto.
Qed.