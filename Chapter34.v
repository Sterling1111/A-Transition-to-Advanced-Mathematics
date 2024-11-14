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

Lemma lemma_34_6_a : limit_of_sequence (fun n => (INR n + 1) / INR n) 1.
Proof.
  intros ε H1. assert (limit_of_sequence (fun n => INR n / INR n) 1) as H2.
  { intros ε2 H2. exists 1. intros n H3. rewrite Rdiv_diag; solve_abs. }
  assert (limit_of_sequence (fun n => 1 / INR n) 0) as H3 by apply theorem_34_12.
  specialize (H2 ε H1) as [N1 H2]. specialize (H3 ε H1) as [N2 H3].
  exists (Rmax N1 (Rmax N2 1)). intros n H4. 
  assert (INR n > N1 /\ INR n > N2 /\ INR n > 1) as [H5 [H6 H7]] by solve_max.
  specialize (H2 n H5). specialize (H3 n H6). replace ((INR n + 1) / INR n - 1) with (1 / INR n) by solve_INR.
  solve_abs.
Qed.

Lemma lemma_34_6_b : convergent_sequence (fun n => (INR n + 1) / INR n).
Proof.
  exists 1. apply lemma_34_6_a.
Qed.

Lemma lemma_34_7 : forall c, limit_of_sequence (fun n => c) c.
Proof.
  apply limit_of_const_sequence.
Qed.

Lemma lemma_34_8 : ~ limit_of_sequence (fun n => INR n) 3.
Proof.
  intros H1. specialize (H1 1 ltac:(lra)) as [N H1]. pose proof INR_unbounded N as [n H2].
  specialize (H1 (max n 4)). assert (INR (max n 4) > N) as H3. 
  { assert ((Nat.max n 4) >= n)%nat as H3. apply Nat.le_max_l. apply le_INR in H3. lra. }
  assert (INR (max n 4) >= 4) as H4. 
  { assert ((Nat.max n 4) >= 4)%nat as H4. apply Nat.le_max_r. apply le_INR in H4. simpl in H4; lra. }
  specialize (H1 H3). solve_abs.
Qed.

Lemma lemma_34_9 : limit_of_sequence (fun n => sqrt (INR n ^ 2 + 1) - INR n) 0.
Proof.
  apply sequence_squeeze with (a := fun n => -1 * (1 / INR n)) (c := fun n => 1 / INR n).
  - replace 0 with (-1 * 0) by lra. apply limit_of_sequence_mul_const. apply theorem_34_12.
  - apply theorem_34_12.
  - exists 1. intros n H1. apply Rplus_ge_reg_r with (r := INR n). field_simplify; try lra.
    rewrite Rdiv_minus_distr. replace (INR n ^ 2 / INR n) with (INR n) by (field_simplify; lra).
    apply Rle_ge. apply Rsqr_incr_0. repeat rewrite Rsqr_def. field_simplify; try nra. rewrite pow2_sqrt; try nra.
    3 : { apply sqrt_pos. } 2 : { apply Rmult_le_reg_r with (r := INR n); field_simplify; try nra. }
    rewrite Rdiv_plus_distr. rewrite Rdiv_minus_distr. replace (INR n ^ 4 / INR n ^ 2) with (INR n ^ 2) by (field_simplify; lra).
    replace (2 * INR n ^ 2 / INR n ^ 2) with 2 by (field_simplify; lra). assert (H2 : 1 / INR n ^ 2 < 1).
    { unfold Rdiv. rewrite Rmult_1_l. replace 1 with (/1) by nra. apply Rinv_lt_contravar; nra. } nra.
  - exists 1. intros n H1. apply Rplus_le_reg_r with (r := INR n); try lra. field_simplify; try lra.
    rewrite Rdiv_plus_distr. replace (INR n ^ 2 / INR n) with (INR n) by (field_simplify; lra).
    apply Rsqr_incr_0. repeat rewrite Rsqr_def. field_simplify; try lra. rewrite pow2_sqrt. 
    3 : { apply sqrt_pos. } 2 : { apply Rmult_le_reg_r with (r := INR n); field_simplify; nra. }
    2 : { apply Rmult_le_reg_r with (r := INR n); field_simplify; nra. } repeat rewrite Rdiv_plus_distr.
    replace (INR n ^ 4 / INR n ^ 2) with (INR n ^ 2) by (field_simplify; lra).
    replace (2 * INR n ^ 2 / INR n ^ 2) with 2 by (field_simplify; lra). assert (H2 : 1 / INR n ^ 2 > 0).
    { unfold Rdiv. rewrite Rmult_1_l. apply Rinv_pos; nra. } nra.
Qed.

Section section_34_10.

  Variable c r : R.
  Variable a : sequence.

  Hypothesis H1 : geometric_sequence a c r.

  Lemma lemma_34_10_c : c > 0 -> r > 1 -> divergent_sequence a.
  Proof.
    unfold geometric_sequence in H1.
    assert (divergent_sequence (fun n => r ^ n)) as H2.
    {
      assert (exists h, r = 1 + h) as [h H3] by (exists (r - 1); lra); subst.
      unfold divergent_sequence. intros L. specialize (H1 L) as [N H1].
    }
    intros H2 H3. unfold geometric_sequence in H1. assert (exists h, r = 1 + h) as [h H4] by (exists (r - 1); lra).
    
  Qed.

  Lemma lemma_34_10_a : |r| < 1 -> limit_of_sequence a 0.
  Proof.
    intros H2. unfold geometric_sequence in H1.
    assert (r > -1 /\ r < 1 /\ (r < 0 \/ r = 0 \/ r > 0)) as [H4 [H5 [H6 | [H6 | H6]]]] by solve_abs.
    - admit.
    - exists 0. intros n H7. replace (a n) with 0; solve_abs. subst. rewrite pow_i; try lra.
      replace 0 with (INR 0) in H7 by auto. apply INR_lt in H7; lia.
    - admit.
  Admitted.
  
  Lemma lemma_34_10_b : c <> 0 -> limit_of_sequence a 0 -> |r| < 1.
  Proof.
    intros H2 H3. assert (|r| = 1 \/ |r| < 1 \/ |r| > 1) as [H4 | [H4 | H4]] by lra; auto.
    - assert (r = 1 \/ r = -1) as [H5 | H5] by solve_abs.
      -- unfold geometric_sequence in H1. subst. replace (fun n : nat => c * 1^n) with (fun n : nat => c) in H3.
         2 : { apply functional_extensionality. intros n. rewrite pow1. lra. } pose proof limit_of_const_sequence c as H6.
         pose proof limit_of_sequence_unique a 0 c H3 H6. subst. apply H1.
         apply limit_of_const_sequence in H3. subst. apply H1.

  Admitted.

  Lemma lemma_34_10_c : c > 0 -> r > 1 -> divergent_sequence a.
  Proof.

  Admitted.

End section_34_10.