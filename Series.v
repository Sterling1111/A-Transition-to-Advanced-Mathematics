Require Import Imports Sums Sequence Reals_util.

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

  Lemma nth_term_in_series_sequence : forall n, partial_sum a n = (INR n + 1).
  Proof.
    unfold partial_sum, a. induction n as [| k IH].
    - sum_simpl. reflexivity.
    - rewrite sum_f_i_Sn_f; try lia. rewrite IH. solve_INR.
  Qed.

  Lemma sequence_of_partial_sums_diverges : series_diverges a.
  Proof.
    intros L. exists 1; split; try lra.
    intros N. pose proof INR_unbounded (Rmax N L) as [n H1]. exists n. split. solve_max.
    rewrite nth_term_in_series_sequence. assert (INR n > L) as H2 by solve_max. solve_abs.
  Qed.
End section_35_2.