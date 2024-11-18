Require Import Imports Sequence Reals_util.
Require Export Chapter20.

Open Scope R_scope.

Ltac compare_elems e1 e2 := 
  let e1' := eval simpl in e1 in
  let e2' := eval simpl in e2 in 
  field_simplify; try nra; try nia.

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

Ltac auto_list :=
  intros; compute;
  try solve [reflexivity];
  compare_lists_step.

Section section_34_1.
  Definition a : sequence := fun n => 5 - 3 * INR n.
  Definition b : sequence := fun n => 4 * 2 ^ n.
  Definition c : sequence := fun n => 1 / 2 + 3 * INR n / 4.
  Definition d : sequence := fun n => (3 / 5) * (2 / 3) ^ n.

  Lemma lemma_34_1_a : map a (seq 0 6) = [5; 2; -1; -4; -7; -10].
  Proof. auto_list. Qed.

  Lemma lemma_34_1_b : map b (seq 0 6) = [4; 8; 16; 32; 64; 128].
  Proof. auto_list. Qed.

  Lemma lemma_34_1_c : map c (seq 0 6) = [2/4; 5/4; 8/4; 11/4; 14/4; 17/4].
  Proof. auto_list. Qed.

  Lemma lemma_34_1_d : map d (seq 0 6) = [3/5; 2/5; 4/15; 8/45; 16/135; 32/405].
  Proof. auto_list. Qed.

End section_34_1.

Section section_34_2.
  Definition prop_34_2_a := ⟦ lim_s ⟧ (fun n => 3 - 4 / INR n) = 3.

  Lemma prop_34_2_a_symbolic : prop_34_2_a = forall ε : ℝ, ε > 0 ⇒ (exists N : ℝ, forall n : ℕ, INR n > N ⇒ Rabs (3 - 4 / INR n - 3) < ε).
  Proof.
    unfold prop_34_2_a, lim_s. reflexivity.
  Qed.
        
  Definition prop_34_2_b := ~ ⟦ lim_s ⟧ (fun n => 6) = 3.
  
  Lemma prop_34_2_b_symbolic : prop_34_2_b = exists ε : ℝ, ε > 0 ⇒ forall N : ℝ, exists n : ℕ, INR n > N ⇒ Rabs (6 - 3) >= ε.
  Proof.
    unfold prop_34_2_b, lim_s. apply EquivThenEqual. split.
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

Lemma lemma_34_4 : ⟦ lim_s ⟧ (fun n => 2 / INR n ^ 2) = 0.
Proof.
  apply sequence_squeeze_lower with (a := fun n => 1 / INR n).
  - apply theorem_34_12.
  - exists 1. intros n H1. apply Rle_ge. apply Rmult_le_reg_r with (r := INR n ^ 2); field_simplify; solve_INR.
    replace 1 with (INR 1) in H1 by auto. apply INR_lt in H1. replace 2 with (INR 2) by auto. apply le_INR in H1. lra.
  - intro n. destruct n. replace (INR 0 ^ 2) with 0 by (simpl; lra). rewrite Rdiv_0_r; lra.
    apply Rlt_le. apply Rdiv_lt_0_compat; try lra. apply pow2_gt_0. pose proof pos_INR n. solve_INR.
Qed.

Lemma lemma_34_5 : ⟦ lim_s ⟧ (fun n => INR (3 * n - 5) / INR (2 * n + 4)) = 3 / 2.
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

Lemma lemma_34_6_a : ⟦ lim_s ⟧ (fun n => (INR n + 1) / INR n) = 1.
Proof.
  intros ε H1. assert (lim_s (fun n => INR n / INR n) 1) as H2.
  { intros ε2 H2. exists 1. intros n H3. rewrite Rdiv_diag; solve_abs. }
  assert (lim_s (fun n => 1 / INR n) 0) as H3 by apply theorem_34_12.
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

Lemma lemma_34_7 : forall c, ⟦ lim_s ⟧ (fun n => c) = c.
Proof.
  apply limit_of_const_sequence.
Qed.

Lemma lemma_34_8 : ~ ⟦ lim_s ⟧ (fun n => INR n) = 3.
Proof.
  intros H1. specialize (H1 1 ltac:(lra)) as [N H1]. pose proof INR_unbounded N as [n H2].
  specialize (H1 (max n 4)). assert (INR (max n 4) > N) as H3. 
  { assert ((Nat.max n 4) >= n)%nat as H3. apply Nat.le_max_l. apply le_INR in H3. lra. }
  assert (INR (max n 4) >= 4) as H4. 
  { assert ((Nat.max n 4) >= 4)%nat as H4. apply Nat.le_max_r. apply le_INR in H4. simpl in H4; lra. }
  specialize (H1 H3). solve_abs.
Qed.

Lemma lemma_34_9 : ⟦ lim_s ⟧ (fun n => sqrt (INR n ^ 2 + 1) - INR n) = 0.
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
    intros H2 H3. apply unbounded_above_divergent_sequence.
    apply geometric_sequence_unbounded_above with (c := c) (r := r); auto.
  Qed.

  Lemma lemma_34_10_a : |r| < 1 -> ⟦ lim_s ⟧ a = 0.
  Proof.
    intros H2. unfold geometric_sequence in H1.
    assert (c = 0 \/ c <> 0) as [H3 | H3] by lra.
    - subst. replace (fun n : nat => 0 * r ^ n) with (fun n : nat => 0).
      2 : { apply functional_extensionality. intros n. lra. }
      apply limit_of_const_sequence.
    - assert (forall a c r, a = (fun n : ℕ => c * r ^ n) -> |r| < 1 -> c <> 0 -> r > 0 -> ⟦ lim_s ⟧ a = 0) as H4.
      {
        clear. intros a c r H1 H2 H3 H4. assert (r < 1) as H5 by solve_abs. set (b := fun n => (1 / c) * (1 / r)^n).
        assert (forall n, b n = 1 / (a n)) as H6.
        { intros n. subst. unfold b. unfold Rdiv. repeat rewrite Rmult_1_l. rewrite Rinv_mult. rewrite pow_inv. lra. }
        assert (c < 0 \/ c > 0) as [H7 | H7] by lra.
        - assert (unbounded_below b) as H8.
          {
            apply geometric_sequence_unbounded_below with (c := 1 / c) (r := 1 / r).
            - apply functional_extensionality. intros n. rewrite H6, H1. unfold Rdiv.
              repeat rewrite Rmult_1_l. rewrite Rinv_mult. rewrite pow_inv. nra.
            - apply Rdiv_pos_neg; lra.
            - apply Rmult_lt_reg_r with (r := r); field_simplify; try lra.
          }
          assert (decreasing b) as H9.
          {
            intros n. unfold b. induction n as [| k IH].
            - field_simplify; try lra. apply Rmult_ge_le_reg_neg_l with (r := c); try lra;
              apply Rmult_le_reg_l with (r := r); field_simplify; try lra.
            - simpl in *. field_simplify; try lra. field_simplify in IH; try lra.
              apply Rmult_ge_le_reg_neg_l with (r := c); try lra; apply Rmult_le_reg_l with (r := r); field_simplify; try lra.
              apply Rge_le in IH. apply Rmult_le_ge_compat_neg_l with (r := c) in IH; try lra. field_simplify in IH; try lra.
          }
          apply limit_of_sequence_reciprocal_unbounded_below_decreasing with (b := b); auto.
        - assert (unbounded_above b) as H8.
          {
            apply geometric_sequence_unbounded_above with (c := 1 / c) (r := 1 / r).
            - apply functional_extensionality. intros n. rewrite H6, H1. unfold Rdiv.
              repeat rewrite Rmult_1_l. rewrite Rinv_mult. rewrite pow_inv. nra.
            - apply Rdiv_pos_pos; lra.
            - apply Rmult_lt_reg_r with (r := r); field_simplify; try lra.
          }
          assert (increasing b) as H9.
          {
            intros n. unfold b. induction n as [| k IH].
            - field_simplify; try lra. apply Rmult_le_reg_r with (r := c); try lra;
              apply Rmult_le_reg_l with (r := r); field_simplify; try lra.
            - simpl in *. field_simplify; try lra. field_simplify in IH; try lra.
              apply Rmult_le_reg_r with (r := c); try lra; apply Rmult_le_reg_l with (r := r); field_simplify; try lra.
              apply Rmult_le_compat_r with (r := c) in IH; try lra. field_simplify in IH; try lra.
          }
          apply limit_of_sequence_reciprocal_unbounded_above_increasing with (b := b); auto.
      }
      assert (r > -1 /\ r < 1 /\ (r > 0 \/ r = 0 \/ r < 0)) as [H5 [H6 [H7 | [H7 | H7]]]] by solve_abs.
      -- apply (H4 a c r); auto.
      -- intros ε H8. exists 0. intros n H9. replace (a n) with 0; solve_abs. subst. rewrite pow_i; try lra.
         replace 0 with (INR 0) in H9 by auto. apply INR_lt in H9; lia.
      -- apply sequence_convergence_comparison with (a := (fun n : ℕ => c * (-r) ^ n)).
         2 : { intros n. rewrite H1. pose proof (Nat.Even_or_Odd n) as [[k H8] | [k H8]].
          - rewrite H8. repeat rewrite pow_Rsqr. replace ((- r)²) with (r²) by (unfold Rsqr; lra). solve_abs.
          - rewrite H8. repeat rewrite pow_add. repeat rewrite pow_Rsqr. replace ((- r)²) with (r²) by (unfold Rsqr; lra). solve_abs.
         }
         specialize (H4 (fun n : ℕ => c * (-r) ^ n) c (-r)) as H8. apply H8; solve_abs. apply functional_extensionality. intros n. reflexivity.
  Qed.

  Lemma lemma_34_10_b : c <> 0 -> ⟦ lim_s ⟧ a = 0 -> |r| < 1.
  Proof.
    intros H2 H3. assert (|r| = 1 \/ |r| < 1 \/ |r| > 1) as [H4 | [H4 | H4]] by lra; auto.
    - assert (r = 1 \/ r = -1) as [H5 | H5] by solve_abs.
      -- unfold geometric_sequence in H1. assert (a = fun n : nat => c) as H6.
          {  apply functional_extensionality. intros n. rewrite H1, H5. rewrite pow1. lra. } 
          rewrite H6 in H3. pose proof limit_of_const_sequence c as H7. assert (c = 0) as H8.
         { apply limit_of_sequence_unique with (a := a); rewrite H6; auto. } lra.
      -- apply oscillating_on_parity_sequence_divergent with (a := (fun n : nat => -c * r^n)) in H2 as H6.
         * replace 0 with (-c * 0) in H3 by lra. apply limit_of_sequence_mul_const_rev with (a := (fun n : nat => r^n)) (L := -c * 0) in H2.
           2 : { repeat rewrite Rmult_0_r in *. rewrite H1 in H3. auto. }
           rewrite divergent_sequence_iff' in H6. specialize (H6 0). exfalso. apply H6.
           replace 0 with (-c * 0) by lra. apply limit_of_sequence_mul_const. rewrite Rmult_0_r in H2. auto.
         * intros n [k H6]. rewrite H6, H5. rewrite pow_add. rewrite pow_mult. simpl. rewrite Rmult_1_r.
           replace (-1 * -1) with 1 by lra. rewrite pow1. lra.
         * intros n [k H6]. rewrite H6, H5. rewrite pow_mult. simpl. replace (-1 * (-1 * 1)) with 1 by lra. rewrite pow1. lra.
    - assert (forall a c r, geometric_sequence a c r -> c <> 0 -> ⟦ lim_s ⟧ a = 0 -> r > 1 -> divergent_sequence a) as H5.
      {
        clear. intros a c r H1 H2 H3 H4. apply unbounded_above_divergent_sequence.
        intros H5. assert (c < 0 \/ c > 0) as [H6 | H6] by lra.
         * apply geometric_sequence_unbounded_below in H1; auto. apply unbounded_below_divergent_sequence in H1.
           rewrite divergent_sequence_iff' in H1. specialize (H1 0). tauto.
         * apply geometric_sequence_unbounded_above in H1; auto.
      }
      assert (r < -1 \/ r > 1) as [H6 | H6] by solve_abs.
      -- set (b := fun n => c * (-r)^n). 
         assert (geometric_sequence b c (-r)) as H7. { apply functional_extensionality. auto. }
         assert (⟦ lim_s ⟧ b = 0) as H8.
         { 
            apply sequence_convergence_comparison with (a := a); auto. intros n. rewrite H1. unfold b.
            repeat rewrite Rminus_0_r. repeat rewrite Rabs_mult. repeat rewrite <- RPow_abs. solve_abs.
         }
         specialize (H5 b c (-r) H7 H2 H8 ltac:(lra)). rewrite divergent_sequence_iff' in H5. specialize (H5 0). tauto.
      -- specialize (H5 a c r H1 H2 H3 H6). rewrite divergent_sequence_iff' in H5. specialize (H5 0). tauto.
  Qed.

End section_34_10.