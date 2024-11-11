Require Import Imports Sequence Reals_util.
Require Export Chapter20.

Open Scope R_scope.

Ltac compare_elems e1 e2 := 
  let e1' := eval simpl in e1 in
  let e2' := eval simpl in e2 in
  first [
    field_simplify; try nra |
    field_simplify; try nia |  
    congruence
  ].

(* Compare two lists recursively element by element *)
Ltac compare_lists_step :=
  match goal with
  | [ |- [] = [] ] => reflexivity
  | [ |- (?x :: ?xs) = (?y :: ?ys) ] => 
      first [
        assert (x = y) by compare_elems x y;
        apply f_equal2; [assumption | compare_lists_step]
        |
        fail "Elements" x "and" y "cannot be proven equal"
      ]
  | [ |- ?l1 = ?l2 ] =>
      fail "Lists" l1 "and" l2 "have different lengths or structures"
  end.

Ltac prove_lists_equal :=
  intros; compute;
  try solve [reflexivity];
  compare_lists_step.

Section section_34_1.
  Definition a : sequence := fun n => 5 - 3 * INR n.
  Definition b : sequence := fun n => 4 * 2 ^ n.
  Definition c : sequence := fun n => 1 / 2 + 3 * INR n / 4.
  Definition d : sequence := fun n => (3 / 5) * (2 / 3) ^ n.

  Lemma lemma_34_1_a : map a (seq 0 6) = [5; 2; -1; -4; -7; -10].
  Proof. prove_lists_equal. Qed.

  Lemma lemma_34_1_b : map b (seq 0 6) = [4; 8; 16; 32; 64; 128].
  Proof. prove_lists_equal. Qed.

  Lemma lemma_34_1_c : map c (seq 0 6) = [2/4; 5/4; 8/4; 11/4; 14/4; 17/4].
  Proof. prove_lists_equal. Qed.

  Lemma lemma_34_1_d : map d (seq 0 6) = [3/5; 2/5; 4/15; 8/45; 16/135; 32/405].
  Proof. prove_lists_equal. Qed.

End section_34_1.

Section section_34_2.
  Definition prop_34_2_a := limit_of_sequence (fun n => 3 - 4 / INR n) 3.

  Lemma prop_34_2_a_symbolic : prop_34_2_a = forall ε : ℝ, ε > 0 ⇒ (exists N : ℝ, forall n : ℕ, INR n > N ⇒ Rabs (3 - 4 / INR n - 3) < ε).
  Proof.
    unfold prop_34_2_a, limit_of_sequence. reflexivity.
  Qed.
        
  Definition prop_34_2_b := ~limit_of_sequence (fun n => 6) 3.
  
  Lemma prop_34_2_b_symbolic : prop_34_2_b = exists ε : ℝ, ε > 0 ⇒ forall N : ℝ, exists n : ℕ, INR n > N ⇒ Rabs (6 - 3) >= ε.
  Proof.
    unfold prop_34_2_b, limit_of_sequence. apply EquivThenEqual. split.
    - intros _. exists 1. intros _. intros N. exists 0%nat. intros _. rewrite Rabs_pos_eq; lra.
    - intros [ε H1] H2. specialize (H2 1 ltac:(lra)) as [N H2]. pose proof INR_unbounded N as [n H3].
      specialize (H2 n H3). rewrite Rabs_pos_eq in H2; lra.
  Qed.
End section_34_2.

Lemma lemma_34_3_a : forall a b,
  Rmax a b >= a /\ Rmax a b >= b.
Proof.
  intros a b. unfold Rmax. destruct (Rle_dec a b); lra.
Qed.

Lemma lemma_34_3_b : forall a b,
  Rmin a b <= a /\ Rmin a b <= b.
Proof.
  intros a b. unfold Rmin. destruct (Rle_dec a b); lra.
Qed.

Lemma lemma_34_3_c : forall a b x,
  x > Rmax a b -> x > a /\ x > b.
Proof.
  intros a b x H1. unfold Rmax in H1. destruct (Rle_dec a b); lra.
Qed.

Lemma lemma_34_4 : limit_of_sequence (fun n => 2 / INR n ^ 2) 0.
Proof.
  apply sequence_squeeze_lower with (a := fun n => 1 / INR n).
  - apply theorem_34_12.
  - exists 1. intros n H1. apply Rle_ge. apply Rmult_le_reg_r with (r := INR n ^ 2); field_simplify; solve_INR.
    replace 1 with (INR 1) in H1 by auto. apply INR_lt in H1. replace 2 with (INR 2) by auto. apply le_INR in H1. lra.
  - intro n. destruct n. replace (INR 0 ^ 2) with 0 by (simpl; lra). rewrite Rdiv_0_r; lra.
    apply Rlt_le. apply Rdiv_lt_0_compat; try lra. apply pow2_gt_0. pose proof pos_INR n. solve_INR.
Qed.

Lemma lemma_34_5 : limit_of_sequence (fun n => INR (3 * n - 5) / INR (2 * n + 4)) (3 / 2).
Proof.
  apply sequence_squeeze with (a := fun n => 3 / 2 - 6 * (1 / INR n)) (c := fun n => 3 / 2).
  - set (a := fun n : nat => 3 / 2). set (b := fun n : nat => 1 / INR n).
    replace ((fun n : ℕ => 3 / 2 - 1 / INR n)) with (fun n : ℕ => a n - b n) by reflexivity.
    replace (3 / 2) with (3/2 - (6 * 0)) at 1 by lra. apply limit_of_sequence_sub;
    [ apply limit_of_const_sequence | apply limit_of_sequence_mul_const; apply theorem_34_12 ].
  - apply limit_of_const_sequence.
  - exists 2. intros n H1. assert (n > 2)%nat as H2. { replace 2 with (INR 2) in H1 by auto. apply INR_lt in H1. lia. }
    break_INR_simpl. apply Rle_ge. apply Rmult_le_reg_r with (r := 2 * INR n); try lra. apply Rmult_le_reg_r with (r := 2 * INR n + 4); field_simplify; nra.
  - exists 1. intros n H1. assert (n > 1)%nat as H2. { replace 1 with (INR 1) in H1 by auto. apply INR_lt in H1. lia. }
    break_INR_simpl. apply Rmult_le_reg_r with (r := 2); try lra. apply Rmult_le_reg_r with (r := 2 * INR n + 4); field_simplify; nra.
Qed.