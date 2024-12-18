Require Import Imports Sums.

Definition is_natural (r : R) : Prop :=
    exists n : nat, r = INR n.

Lemma is_natural_plus : forall r1 r2 : R,
  is_natural r1 -> is_natural r2 -> is_natural (r1 + r2).
Proof.
  intros r1 r2 H1 H2. destruct H1 as [n1 H1]. destruct H2 as [n2 H2]. exists (n1 + n2)%nat. rewrite H1, H2. rewrite plus_INR. reflexivity.
Qed.

Lemma is_natural_sum_n_nat : forall n : nat,
  (n >= 1)%nat -> is_natural (sum_f 1 n (fun i => INR i)).
Proof.
  intros n H1. induction n as [| k IH]; try lia.
  assert (S k = 1 \/ k >= 1)%nat as [H2 | H2] by lia.
  - rewrite H2. exists 1%nat. compute. reflexivity.
  - rewrite sum_f_i_Sn_f; try lia. apply is_natural_plus; auto. exists (S k). reflexivity.
Qed.

Lemma nltb_gt : forall a b : nat, (a > b)%nat <-> (a <=? b) = false.
Proof.
  intros a b. split.
  - intros H1. apply leb_correct_conv; lia.
  - intros H1. destruct (Nat.leb_spec a b); try lia. 
Qed.

Lemma nltb_ge : forall a b : nat, (a >= b)%nat <-> (a <? b) = false.
Proof.
  intros a b. split.
  - intros H1. apply leb_correct_conv; lia.
  - intros H1. destruct (Nat.ltb_spec a b); try lia.
Qed.

Module Binomial_R.
  Open Scope R_scope.

  Definition choose (n k : nat) : R :=
    if (n <? k) then 0 else
    (INR (fact n)) / (INR (fact k) * INR (fact (n - k))).

  Module Choose_R_Notations.

    Notation "n ∁ r" := (choose n r) (at level 10).

  End Choose_R_Notations.

  Import Choose_R_Notations.

  Lemma n_choose_n : forall (n : nat),
    n ∁ n = 1.
  Proof.
    intro n. unfold choose. replace (n - n)%nat with 0%nat by lia.
    simpl. rewrite Rmult_1_r. rewrite Nat.ltb_irrefl.
    field. apply INR_fact_neq_0.
  Qed.

  Lemma Sn_choose_n : forall (n : nat),
    (S n) ∁ n = INR (S n).
  Proof.
    intro n. unfold choose. assert (S n <? n = false) as H1. apply Nat.ltb_ge. lia. rewrite H1. replace (S n - n)%nat with 1%nat by lia.
    replace (fact 1) with 1%nat by reflexivity. replace (fact (S n)) with ((S n) * fact n)%nat. 2 : { simpl. reflexivity. }
    rewrite mult_INR. unfold Rdiv. rewrite Rmult_assoc. field_simplify. replace (INR 1) with 1 by reflexivity. nra. split. apply not_0_INR. lia. apply not_0_INR.
    apply fact_neq_0.
  Qed.

  Lemma n_choose_0 : forall (n : nat),
    n ∁ 0 = 1.
  Proof.
    intro n. unfold choose. simpl. rewrite Nat.sub_0_r. rewrite Rmult_1_l.
    field. apply INR_fact_neq_0.
  Qed.

  Lemma O_choose_n : forall (n : nat),
    (n <> 0)%nat -> 0 ∁ n = 0.
  Proof.
    intros n H1. unfold choose. simpl. destruct n; try lia; simpl. lra.
  Qed.

  Lemma k_gt_n_n_choose_k : forall n k : nat,
    (n < k)%nat -> n ∁ k = 0.
  Proof.
    intros. assert (H2 : n <? k = true).
    { apply Nat.ltb_lt. apply H. }
    unfold choose. rewrite H2. reflexivity.
  Qed.

  Lemma n_choose_k_def : forall n k : nat,
    (n >= k)%nat -> n ∁ k = INR (fact n) / (INR (fact k) * INR (fact (n - k))).
  Proof.
    intros n k H1. unfold choose. apply nltb_ge in H1. rewrite H1. reflexivity.
  Qed.

  Lemma fact_div' : forall m n k,
    (k >= 1)%nat -> (m <> 0) -> n / ((INR (fact (k - 1))) * m)  = (n * INR (k)) / (INR (fact k) * m).
  Proof.
    intros m n k H1 H2. destruct k.
    - lia.
    - destruct k.
      -- simpl. lra.
      -- replace (fact (S (S k))) with ((S (S k)) * fact (S k))%nat. 2 : { simpl. lia. }
        replace (S (S k) - 1)%nat with (S ((S k) - 1))%nat. 2 : { simpl. lia. }
      replace (S (S k - 1))%nat with (S k) by lia. unfold Rdiv.
      replace (n * INR (S (S k)) * / (INR (S (S k) * fact (S k)) * m)) with (n * / (INR (fact (S k)) * m)).
      2 : { rewrite mult_INR. field. split. pose proof fact_neq_0 as H3. apply H2. split. apply not_0_INR. apply fact_neq_0. apply not_0_INR. lia. }
      reflexivity.
  Qed.

  Lemma binomial_recursion_R_1 : forall n k : nat,
    (k >= 1)%nat -> (S n) ∁ k = n ∁ (k - 1) + n ∁ k.
  Proof.
    intros. assert (H2 : (S n < k \/ S n = k \/ S n > k)%nat) by lia. destruct H2 as [H2 | [H2 | H2]].
    - repeat rewrite k_gt_n_n_choose_k. lra. lia. lia. lia.
    - assert (H3 : (n = k - 1)%nat) by lia. rewrite <- H3. rewrite H2. repeat rewrite n_choose_n.
      rewrite k_gt_n_n_choose_k. lra. lia.
    - unfold choose at 2.
      assert (H3 : (n >= k - 1)%nat) by lia. pose proof H3 as H4. apply nltb_ge in H4.
      rewrite H4. unfold choose at 2. assert (H5 : (n >= k)%nat) by lia. pose proof H5 as H6.
      apply nltb_ge in H6. rewrite H6. rewrite fact_div'. 2 : { lia. } 2 : { apply not_0_INR. apply fact_neq_0. }
      assert (H7: (n = k)%nat \/ (n > k)%nat) by lia. destruct H7 as [H7 | H7].
      -- rewrite H7. replace ((k - k)%nat) with 0%nat by lia. replace (k - (k - 1))%nat with (1)%nat by lia.
        simpl. repeat rewrite Rmult_1_r. unfold choose. assert (H8 : S k <? k = false). apply nltb_gt. lia.
        rewrite H8. replace (S k - k)%nat with 1%nat by lia. simpl. rewrite Rmult_1_r. rewrite plus_INR.
        rewrite mult_INR. nra.
      -- replace (n - k)%nat with (S (n - k) - 1)%nat by lia. rewrite Rmult_comm with (r2 := INR (fact (S (n - k) - 1))).
        rewrite fact_div' with (n := INR (fact n)).
        2 : { lia. } 2 : { apply not_0_INR. apply fact_neq_0. }
        replace (S (n - k))%nat with (n - (k - 1))%nat at 2 by lia.
        rewrite Rmult_comm with (r2 := INR (fact k)).
        replace (INR (fact n) * INR k / (INR (fact k) * INR (fact (n - (k - 1)))) + INR (fact n) * INR (S (n - k)) / (INR (fact k) * INR (fact (n - (k - 1))))) with
        ((INR (fact n) * INR k + INR (fact n) * INR (S (n - k))) / (INR (fact k) * INR (fact (n - (k - 1))))).
        2 : { nra. }
        rewrite <- Rmult_plus_distr_l. rewrite <- plus_INR. replace (k + S (n - k))%nat with (S n)%nat by lia.
        replace (INR (fact n) * INR (S n)) with (INR (fact (S n))). 2 : { rewrite <- mult_INR. simpl. replace (fact n * S n)%nat with (fact n + n * fact n)%nat by lia.
        reflexivity. }
        unfold choose. assert (H8 : S n <? k = false). apply nltb_gt. lia. rewrite H8.
        replace (n - (k - 1))%nat with (S n - k)%nat by lia. reflexivity.
  Qed.

  Lemma binomial_recursion_R_2 : forall n k : nat,
    (k >= 1)%nat -> choose n (S k) = choose (S n) (S k) - n ∁ k.
  Proof.
    intros n k H1. rewrite binomial_recursion_R_1. 2 : { lia. } replace (S k - 1)%nat with k by lia. lra.
  Qed.

  Lemma n_choose_1 : forall (n : nat),
    n ∁ 1 = INR n.
  Proof.
    intro n. induction n as [| k IH].
    - compute. lra.
    - rewrite binomial_recursion_R_1; try lia. rewrite IH. replace (1 - 1)%nat with 0%nat by lia. rewrite n_choose_0. rewrite S_INR. lra.
  Qed.

  Lemma choose_natural : forall n k : nat,
    is_natural (n ∁ k).
  Proof.
    intros n k. assert ((n < k \/ n = k \/ n > k)%nat) as [H1 | [H1 | H1]] by lia.
    - exists 0%nat. rewrite k_gt_n_n_choose_k; try lia. reflexivity.
    - exists 1%nat. rewrite H1. rewrite n_choose_n. reflexivity.
    - generalize dependent k. induction n as [| n' IH].
      -- intros n H1. exists 0%nat. rewrite O_choose_n; lia.
      -- intros n H1. assert (n = 0 \/ n >= 1)%nat as [H2 | H2] by lia.
        + rewrite H2. exists 1%nat. rewrite n_choose_0. reflexivity.
        + assert (n' = n \/ n' > n)%nat as [H3 | H3] by lia.
          * rewrite binomial_recursion_R_1; try lia. rewrite H3 at 2. rewrite n_choose_n. specialize (IH (n - 1)%nat). destruct IH as [m H4]; try lia.
            exists (m+1)%nat. rewrite H4. rewrite plus_INR. reflexivity.
          * rewrite binomial_recursion_R_1; try lia. pose proof IH as IH2. specialize (IH n). specialize (IH2 (n-1)%nat). destruct IH as [m H4]; try lia.
            destruct IH2 as [m' H5]; try lia. exists (m + m')%nat. rewrite H4. rewrite H5. rewrite plus_INR. lra.
  Qed.

  Lemma pow_equ : forall (r: R) (a : nat),
    (a > 0)%nat -> r ^ a = r * r ^ (a - 1).
  Proof.
    intros r a H1. destruct a.
    - lia.
    - simpl. rewrite Nat.sub_0_r. reflexivity.
  Qed.

  Theorem Binomial_Theorem_R : forall a b n,
    (a + b) ^ n = sum_f 0 n (fun i => (choose n i) * a ^ (n - i) * b ^ i).
  Proof.
    intros a b n. induction n as [| k IH].
    - compute; lra.
    - replace ((a + b) ^ (S k)) with ((a + b) * (a + b) ^ k) by (simpl; lra).
      rewrite Rmult_plus_distr_r. repeat rewrite IH. repeat rewrite r_mult_sum_f_i_n_f.
      replace (fun i : nat => choose k i * a ^ (k - i) * b ^ i * a) with (fun i : nat => choose k i * a ^ (k - i + 1) * b ^ i).
      2 : { apply functional_extensionality. intros x. replace (choose k x * a ^ (k - x) * b ^ x * a) with (choose k x * (a ^ (k - x) * a) * b ^ x) by lra.
            replace (k - x + 1)%nat with (S (k - x))%nat by lia. rewrite <- tech_pow_Rmult. lra. }
      replace (fun i : nat => choose k i * a ^ (k - i) * b ^ i * b) with (fun i : nat => choose k i * a ^ (k - i) * b ^ (i + 1)).
      2 : { apply functional_extensionality. intros x. replace (choose k x * a ^ (k - x) * b ^ x * b) with (choose k x * a ^ (k - x) * (b ^ x * b)) by lra.
            replace (x + 1)%nat with (S x) by lia. rewrite <- tech_pow_Rmult. lra. }
      replace (sum_f 0 k (fun i : nat => choose k i * a ^ (k - i) * b ^ (i + 1))) with
      (sum_f 1 (k + 1) (fun i : nat => choose k (i-1) * a ^ (k - (i-1)) * b ^ (i))).
      2 : { rewrite sum_f_reindex' with (i := 0%nat) (n := k%nat) (s := 1%nat). simpl.
      set (f := fun i : nat => choose k (i - 1) * a ^ (k - (i - 1)) * b ^ i).
      set (g := fun x : nat => choose k (x - 1) * a ^ (k - (x - 1)) * b ^ (x - 1 + 1)).
      apply sum_f_equiv.
      - lia.
      - intros k0 H. unfold f, g. replace (k0 - 1 + 1)%nat with (k0) by lia. reflexivity. }
      destruct k as [| k'] eqn:Ek.
      -- compute. lra.
      -- rewrite sum_f_Si. 2 : { lia. }
        replace (S k' + 1)%nat with (S (k' + 1))%nat by lia.
        destruct k' as [| k''] eqn:Ek''.
        --- compute. lra.
        --- rewrite sum_f_i_Sn_f with (n := (S (k'' + 1))%nat). 2 : { lia. }
            repeat rewrite <- Ek. repeat replace ((S (k'' + 1))%nat) with (k)%nat by lia.
            replace (sum_f 1 k (fun i : nat => choose k i * a ^ (k - i + 1) * b ^ i) + choose k 0 * a ^ (k - 0 + 1) * b ^ 0 +
            (sum_f 1 k (fun i : nat => choose k (i - 1) * a ^ (k - (i - 1)) * b ^ i) + choose k (S k - 1) * a ^ (k - (S k - 1)) * b ^ S k))
            with (sum_f 1 k (fun i : nat => choose k i * a ^ (k - i + 1) * b ^ i) + sum_f 1 k (fun i : nat => choose k (i - 1) * a ^ (k - (i - 1)) * b ^ i) +
            choose k 0 * a ^ (k - 0 + 1) * b ^ 0 + choose k (S k - 1) * a ^ (k - (S k - 1)) * b ^ S k) by lra.
            rewrite sum_f_sum. assert (H2 : sum_f 1 k (fun x : nat => choose k x * a ^ (k - x + 1) * b ^ x + choose k (x - 1) * a ^ (k - (x - 1)) * b ^ x)
            = sum_f 1 k (fun x : nat => choose (S k) x * a ^ (k - x + 1) * b ^ x)).
            { apply sum_f_equiv. lia. intros k0 H2. replace (k - (k0 - 1))%nat with (k - k0 + 1)%nat by lia.
            rewrite Rmult_assoc. rewrite Rmult_assoc with (r1 := choose k (k0 - 1)) at 1.
            rewrite <- Rmult_plus_distr_r with (r3 := a ^ (k - k0 + 1) * b ^ k0). rewrite Rplus_comm. rewrite binomial_recursion_R_1. 2 : { lia. } lra. }
            rewrite H2. rewrite sum_f_Si_n_f. 2 : { lia. } rewrite sum_f_i_Sn_f. 2 : { lia. } replace (choose (S k) (S k)) with 1. 2 : { rewrite n_choose_n. auto. }
            replace (choose (S k) 0%nat) with 1. 2 : { rewrite n_choose_0. reflexivity. }
            repeat rewrite Rmult_1_l. replace (k - (S k - 1))%nat with 0%nat by lia. replace (S k - S k)%nat with 0%nat by lia.
            replace (b ^ 0) with 1 by auto. replace (a ^ 0) with 1 by auto. rewrite Rmult_1_l. repeat rewrite Rmult_1_r.
            replace (k - 0 + 1)%nat with (S k) by lia. replace (S k - 1)%nat with k%nat by lia. rewrite n_choose_n. rewrite Rmult_1_l. rewrite n_choose_0.
            rewrite Rmult_1_l. replace (sum_f 0 k (fun x : nat => choose (S k) x * a ^ (k - x + 1) * b ^ x)) with (sum_f 0 k (fun i : nat => choose (S k) i * a ^ (S k - i) * b ^ i)).
            2 : { apply sum_f_equiv. lia. intros k0 H3. replace (S k - k0)%nat with (k - k0 + 1)%nat by lia. reflexivity. }
            nra.
  Qed.

  Lemma fact_ge_1 : forall n : nat, (fact n >= 1)%nat.
  Proof.
    induction n as [| k IH]; (simpl; lia).
  Qed.

  Lemma fact_2n_gt_fact_n_pow2 : forall n : nat,
    (n >= 1)%nat -> (fact (2 * n) > fact n * fact n)%nat.
  Proof.
    intros n H1. induction n as [| k IH]; try lia.
    assert (S k = 1 \/ S k > 1)%nat as [H2 | H2] by lia.
    - rewrite H2. simpl. lia.
    - specialize (IH ltac : (lia)). replace (2 * S k)%nat with (S (S (2 * k)))%nat by lia. repeat rewrite fact_simpl. nia.
  Qed.

  Lemma factorial_product_inequality_le : forall n k : nat,
    (k < n)%nat -> INR (fact n) * INR (fact n) <= INR (fact k) * INR (fact (2 * n - k)).
  Proof.
    intros n k H1. induction n as [| n IH]; try lia.
    assert (H2 : (n = k \/ n > k)%nat) by lia. destruct H2 as [H2 | H2].
    - rewrite H2. replace (2 * S k - k)%nat with (S(S k)) by lia. repeat rewrite fact_simpl. repeat rewrite mult_INR. repeat rewrite S_INR.
      pose proof (fact_ge_1 k) as H3. assert (INR 1 <= INR (fact k)) as H4. { apply le_INR. apply H3. } simpl in H4.
      assert (0 <= INR k). { apply pos_INR. } nra.
    - specialize (IH ltac : (lia)). replace (2 * S n - k)%nat with (S (S (2 * n - k)))%nat by lia. repeat rewrite fact_simpl.
      repeat rewrite mult_INR. assert (INR (S n) * INR (S n) <= (INR (S (S (2 * n - k))) * (INR (S (2 * n - k))))).
      { repeat rewrite S_INR. repeat rewrite minus_INR; try lia. repeat rewrite mult_INR. simpl. apply lt_INR in H2. pose proof (pos_INR k) as H3. nra. }
      nra.
  Qed.

  Lemma fact_n_gt_0 : forall n : nat,
    (n > 0)%nat -> (0 < fact n)%nat.
  Proof.
    intros n H1. induction n as [| k IH]; try lia.
    assert (k = 0 \/ k > 0)%nat as [H2 | H2] by lia.
    - subst. simpl. lia.
    - simpl. lia.
  Qed.

  Lemma n_choose_k_ge_0 : forall n k : nat,
    n ∁ k >= 0.
  Proof.
    intros n k. unfold choose. destruct (n <? k) eqn:H1.
    - lra.
    - pose proof (fact_ge_1 n) as H2. pose proof (fact_ge_1 k) as H3. pose proof (fact_ge_1 (n - k)) as H4.
      apply le_INR in H2, H3, H4. simpl in *. apply Rle_ge. apply Rmult_le_reg_r with (r := INR (fact k) * INR (fact (n - k))); try nra.
      field_simplify; nra.
  Qed.

  Lemma n_choose_k_ge_1 : forall n k : nat,
    (k <= n)%nat -> (n ∁ k >= 1)%R.
  Proof.
    intros n k H1. induction n as [| n IH].
    - replace k with 0%nat by lia. rewrite n_choose_0. lra.
    - assert ((k = S n \/ k < S n)%nat) as [H2 | H2] by lia.
      -- rewrite H2. rewrite n_choose_n. lra.
      -- assert (k = 0 \/ k >= 1)%nat as [H3 | H3] by lia.
         * rewrite H3. rewrite n_choose_0. lra.
         * specialize (IH ltac : (lia)). rewrite binomial_recursion_R_1; try lia. pose proof (n_choose_k_ge_0 n (k - 1)). nra.
  Qed.

Lemma n_choose_k_sym : forall n k,
  (n >= k)%nat -> n ∁ k = n ∁ (n - k).
Proof.
  intros n k H1. repeat rewrite n_choose_k_def; try lia.
  replace (n - (n - k))%nat with k by lia. field. split. apply not_0_INR. apply fact_neq_0. apply not_0_INR. apply fact_neq_0.
Qed.

Lemma n_choose_k_max_le : forall n k : nat,
  (k <= n / 2)%nat -> n ∁ (n / 2) >= n ∁ k.
Proof.
  intros n k H1. pose proof (Nat.Even_or_Odd n) as [[m H2] | [m H2]].
  - rewrite H2. replace (2 * m / 2)%nat with m. 2 : { rewrite Nat.mul_comm. rewrite Nat.div_mul; auto. }
    rewrite H2 in H1. rewrite Nat.mul_comm in H1. rewrite Nat.div_mul in H1; auto.
    assert (k = m \/ k < m)%nat as [H3 | H3] by lia.
    -- subst. lra.
    -- assert (k = 0 \/ k > 0)%nat as [H4 | H4] by lia.
       * rewrite H4. rewrite n_choose_0. apply Rle_ge. pose proof (n_choose_k_ge_1 (2 * m) m) as H5. specialize (H5 ltac : (lia)). nra.
       * repeat rewrite n_choose_k_def; try lia. replace (2 * m - m)%nat with m by lia.
         pose proof (factorial_product_inequality_le m k H3) as H5. assert (0 <= INR (fact (2 * m))) as H6. { apply pos_INR. }
         assert (0 < (INR (fact m) * INR (fact m))) as H7. { rewrite <- mult_INR. apply lt_0_INR. apply Nat.mul_pos_pos; (apply fact_n_gt_0; lia). }
         apply Rmult_le_compat_r with (r := INR (fact (2 * m))) in H5; try nra. apply Rle_ge. apply Rmult_le_reg_r with (r := INR (fact m) * INR (fact m)); try lra.
         apply Rmult_le_reg_r with (r := (INR (fact k) * INR (fact (2 * m - k)))).
         rewrite <- mult_INR. apply lt_0_INR. apply Nat.mul_pos_pos. apply fact_n_gt_0. lia.
         2 : { field_simplify. nra. apply not_0_INR. apply fact_neq_0. split. apply not_0_INR. apply fact_neq_0. apply not_0_INR. apply fact_neq_0. }
         pose proof (fact_ge_1 (2 * m - k)) as H8. lia.
  - rewrite H2. replace (2 * m / 2)%nat with m. 2 : { rewrite Nat.mul_comm. rewrite Nat.div_mul; auto. }
    rewrite H2 in H1. assert ((2 * m + 1) / 2 = m)%nat as H3.
    {  rewrite <- Nat.div2_div. replace (2 * m + 1 )%nat with (S (2 * m)) by lia. rewrite Nat.div2_succ_double. lia. }
    rewrite H3 in *. 
    assert (k = m \/ k < m)%nat as [H4 | H4] by lia.
    -- subst. lra.
    -- assert (k = 0 \/ k > 0)%nat as [H5 | H5] by lia.
       * rewrite H5. rewrite n_choose_0. apply Rle_ge. pose proof (n_choose_k_ge_1 (2 * m + 1) m) as H6. specialize (H6 ltac : (lia)). nra.
       * repeat rewrite n_choose_k_def; try lia. replace (2 * m + 1 - m)%nat with (S m) by lia.
         pose proof (factorial_product_inequality_le m k H4) as H6. assert (0 <= INR (fact (2 * m + 1))) as H7. { apply pos_INR. }
         assert (0 < (INR (fact m) * INR (fact (S m)))) as H8. { rewrite <- mult_INR. apply lt_0_INR. apply Nat.mul_pos_pos; (apply fact_n_gt_0; lia). }
         apply Rmult_le_compat_r with (r := INR (fact (2 * m + 1))) in H6; try nra. apply Rle_ge. apply Rmult_le_reg_r with (r := INR (fact m) * INR (fact (S m))); try lra.
         apply Rmult_le_reg_r with (r := (INR (fact k) * INR (fact (2 * m + 1 - k)))).
         rewrite <- mult_INR. apply lt_0_INR. apply Nat.mul_pos_pos. apply fact_n_gt_0. lia. apply fact_n_gt_0. lia.
         field_simplify. replace (2 * m + 1 - k)%nat with (S (2 * m - k))%nat by lia. repeat rewrite fact_simpl. repeat rewrite mult_INR.
         assert (INR (S m) <= INR (S (2 * m - k))) as H9. { apply le_INR. lia. } assert (0 < INR (S m)) as H10. { apply lt_0_INR. lia. }
         assert (0 < INR (S (2 * m - k))) as H11. { apply lt_0_INR. lia. }
         replace (INR (fact (2 * m + 1)) * INR (fact m) * (INR (S m) * INR (fact m))) with (INR (S m) * (INR (fact (2 * m + 1)) * INR (fact m) * INR (fact m))) by nra.
         replace (INR (fact (2 * m + 1)) * INR (fact k) * (INR (S (2 * m - k)) * INR (fact (2 * m - k)))) with ((INR (S (2 * m - k)) * (INR (fact (2 * m + 1)) * INR (fact k) * INR (fact (2 * m - k))))) by nra.
         apply Rmult_le_compat; try nra. split; apply INR_fact_neq_0. split; apply INR_fact_neq_0.
  Qed.
  
  Lemma n_choose_k_max_gt : forall n k : nat,
    (k > n / 2)%nat -> n ∁ (n / 2) >= n ∁ k.
  Proof.
    intros n k H1. assert (k > n \/ k <= n)%nat as [H2 | H2] by lia.
    - rewrite k_gt_n_n_choose_k with (k := k); try lia. apply n_choose_k_ge_0.
    - rewrite n_choose_k_sym with (k := k); try lia. apply n_choose_k_max_le. pose proof (Nat.Even_or_Odd n) as [[m H3] | [m H3]].
      -- rewrite H3. rewrite H3 in H1. rewrite Nat.mul_comm in H1. rewrite Nat.div_mul in H1; try lia. rewrite Nat.mul_comm.
         rewrite Nat.div_mul; try lia.
      -- rewrite H3. rewrite H3 in H1. assert ((2 * m + 1) / 2 = m)%nat as H4.
         {  rewrite <- Nat.div2_div. replace (2 * m + 1 )%nat with (S (2 * m)) by lia. rewrite Nat.div2_succ_double. lia. } lia.
  Qed.

  Lemma n_choose_k_max : forall n k : nat,
    n ∁ (n / 2) >= n ∁ k.
  Proof.
    intros n k. assert (k <= n / 2 \/ k > n / 2)%nat as [H1 | H1] by lia.
    - apply n_choose_k_max_le. apply H1.
    - apply n_choose_k_max_gt. apply H1.
  Qed.

End Binomial_R.

Lemma Rdiv_natdiv : forall n1 n2 : nat,
  (n2 <> 0)%nat ->
  is_natural (INR (n1) / INR (n2)) -> Nat.divide n2 n1.
Proof.
  intros n1 n2 H1 [k H2]. exists k.  apply Rmult_eq_compat_r with (r := INR n2) in H2.
  field_simplify in H2. 2 : { apply not_0_INR; lia. } rewrite <- mult_INR in H2. apply INR_eq in H2. lia.
Qed.

Lemma fact_geq_1 : forall n : nat, (fact n >= 1)%nat.
Proof.
  induction n as [| k IH]; (simpl; lia).
Qed.

Lemma div_INR : forall n m : nat,
  (m <> 0)%nat -> (Nat.divide m n) -> INR (n / m) = INR n / INR m.
Proof.
  intros n m H1 [k H2]. rewrite H2. rewrite Nat.div_mul; auto. rewrite mult_INR. field. apply not_0_INR. lia.
Qed.

Lemma fact_div : forall (n k : nat),
  (k <= n)%nat -> Nat.divide (fact k * fact (n - k)) (fact n).
Proof.
  intros n k H1. apply Rdiv_natdiv. pose proof (fact_neq_0 k) as H2. pose proof (fact_neq_0 (n - k)) as H3. lia.
  rewrite mult_INR. replace (INR (fact n) / (INR (fact k) * INR (fact (n - k)))) with (Binomial_R.choose n k).
  2 : { unfold Binomial_R.choose. apply nltb_ge in H1. rewrite H1. reflexivity. }
  apply Binomial_R.choose_natural.
Qed.

Import Binomial_R.

Open Scope nat_scope.

Definition choose (n k : nat) : nat :=
if (n <? k) then 0 else
(fact n) / ((fact k) * (fact (n - k))).

Module Choose_Notations.

  Notation "n ∁ r" := (choose n r) (at level 10).

End Choose_Notations.

Import Choose_Notations.

Lemma Choose_N_eq_Choose_R : forall n k : nat,
  INR (n ∁ k) = Binomial_R.choose n k.
Proof.
  intros n k. unfold choose, Binomial_R.choose. destruct (n <? k) eqn:H1; try (simpl; lra).
  apply nltb_ge in H1. pose proof (fact_div n k H1) as H2. rewrite <- mult_INR. rewrite div_INR; try lia; try lra; auto.
  pose proof fact_neq_0 k as H3. pose proof fact_neq_0 (n - k) as H4. lia.
Qed.

Lemma n_choose_n : forall (n : nat),
  n ∁ n = 1.
Proof.
  intro n. pose proof Binomial_R.n_choose_n n as H1. rewrite <- Choose_N_eq_Choose_R in H1. apply INR_eq. auto.
Qed.

Lemma Sn_choose_n : forall (n : nat),
  (S n) ∁ n = S n.
Proof.
  intro n. pose proof Binomial_R.Sn_choose_n n as H1. rewrite <- Choose_N_eq_Choose_R in H1. apply INR_eq. auto.
Qed.

Lemma n_choose_0 : forall (n : nat),
  n ∁ 0 = 1.
Proof.
  intro n. pose proof Binomial_R.n_choose_0 n as H1. rewrite <- Choose_N_eq_Choose_R in H1. apply INR_eq. simpl. auto.
Qed.

Lemma O_choose_n : forall (n : nat),
  n <> 0 -> 0 ∁ n = 0.
Proof.
  intros n H1. pose proof Binomial_R.O_choose_n n H1 as H2. rewrite <- Choose_N_eq_Choose_R in H2. apply INR_eq. simpl. auto.
Qed.

Lemma n_lt_k_choose_k : forall n k : nat,
  n < k -> n ∁ k = 0.
Proof.
  intros n k H1. pose proof Binomial_R.k_gt_n_n_choose_k n k H1 as H2. rewrite <- Choose_N_eq_Choose_R in H2. apply INR_eq. auto.
Qed.

Lemma n_choose_1 : forall (n : nat),
  n ∁ 1 = n.
Proof.
  intro n. pose proof Binomial_R.n_choose_1 n as H1. rewrite <- Choose_N_eq_Choose_R in H1. apply INR_eq. auto.
Qed.

Lemma n_choose_k_def : forall n k : nat,
  n >= k -> n ∁ k = fact n / (fact k * fact (n - k)).
Proof.
  intros n k H1. unfold choose. apply nltb_ge in H1. rewrite H1. reflexivity.
Qed.

Lemma binomial_recursion_1 : forall n k : nat,
  (n + 1) ∁ (k + 1) = n ∁ k + n ∁ (k + 1).
Proof.
  intros n k. assert (k = 0 \/ k >= 1)%nat as [H1 | H1] by lia; subst; simpl.
  - rewrite n_choose_0. repeat rewrite n_choose_1. lia.
  - pose proof Binomial_R.binomial_recursion_R_2 n k H1 as H2. repeat rewrite <- Choose_N_eq_Choose_R in H2. apply INR_eq.
    rewrite plus_INR. replace (S k) with (k + 1)%nat in H2 by lia. replace (S n) with (n + 1)%nat in H2 by lia. lra.
Qed.

Lemma binomial_recursion_2 : forall n k : nat,
  (k >= 1) -> (n + 1) ∁ k = n ∁ k + n ∁ (k - 1).
Proof.
  intros n k H1. pose proof Binomial_R.binomial_recursion_R_1 n k H1 as H2. repeat rewrite <- Choose_N_eq_Choose_R in H2. apply INR_eq.
  rewrite plus_INR. replace (S n) with (n + 1)%nat in H2 by lia. lra.
Qed.

Lemma choose_ge_0 : forall n k : nat,
  n ∁ k >= 0.
Proof.
  intros n k. induction n as [| n IH].
  - assert (k = 0 \/ k >= 1)%nat as [H1 | H1] by lia; subst; simpl. lia. rewrite O_choose_n; lia.
  - assert (k = 0 \/ k >= 1)%nat as [H1 | H1] by lia; subst; simpl.
    + rewrite n_choose_0. lia.
    + pose proof binomial_recursion_2 n k H1 as H2. lia.
Qed.

Lemma binomial_recursion_3 : forall n k : nat,
  n ∁ (k + 1) = (n + 1) ∁ (k + 1) - n ∁ k.
Proof.
  intros n k. assert (k = 0 \/ k >= 1)%nat as [H1 | H1] by lia; subst; simpl.
  - rewrite n_choose_0. repeat rewrite n_choose_1. lia.
  - pose proof Binomial_R.binomial_recursion_R_2 n k H1 as H2. repeat rewrite <- Choose_N_eq_Choose_R in H2. apply INR_eq.
    replace (S k) with (k + 1)%nat in H2 by lia. replace (S n) with (n + 1)%nat in H2 by lia.
    assert (H3 : (n + 1) ∁ (k + 1) >= n ∁ k).
    { rewrite binomial_recursion_1. pose proof choose_ge_0 n k as H4. pose proof choose_ge_0 n (k + 1). lia. }
    rewrite minus_INR; try lia. lra.
Qed.

Lemma binomial_recursion_4 : forall n k : nat,
  n >= 1 -> k >= 1 -> n ∁ k = (n - 1) ∁ (k - 1) + (n - 1) ∁ k.
Proof.
  intros n k H1 H2. pose proof binomial_recursion_2 (n - 1) k H2 as H3.
  replace (n - 1 + 1) with n in H3 by lia. lia.
Qed.

Open Scope R_scope.

Theorem Binomial_Theorem : forall a b n,
  (a + b) ^ n = sum_f 0 n (fun i => INR (n ∁ i) * a ^ (n - i) * b ^ i).
Proof.
  intros a b n. pose proof Binomial_R.Binomial_Theorem_R a b n as H1. rewrite H1. apply sum_f_equiv. lia. intros i H2.
  rewrite <- Choose_N_eq_Choose_R. lra.
Qed.

Ltac simplify_nat_choose :=
  repeat match goal with
         | [ |- context[(?n ∁ ?k)] ] =>
           let C := eval compute in (choose n k) in
           change (n ∁ k) with C
         end.

Ltac simplify_power_expr :=
  repeat match goal with
  | |- context[?base ^ (?n - ?m)] =>
    let result := eval compute in (n - m)%nat in
    replace ((n - m)%nat) with (result) by (
      simpl; lia
    )
  end.

Ltac simplify_binomial_expansion :=
  rewrite Binomial_Theorem; repeat rewrite sum_f_i_Sn_f; try lia; rewrite sum_f_0_0; simplify_nat_choose; unfold INR; simplify_power_expr; field_simplify.

Open Scope nat_scope.

Lemma choose_n_max : forall n k : nat,
  n ∁ (n / 2) >= n ∁ k.
Proof.
  intros n k. pose proof Binomial_R.n_choose_k_max n k as H1. repeat rewrite <- Choose_N_eq_Choose_R in H1. apply INR_le. lra.
Qed.

Fixpoint Z_fact (n : nat) : Z :=
  match n with
  | 0%nat => 1%Z
  | S n' => Z.of_nat (S n') * Z_fact n'
  end.

Open Scope Z_scope.

Lemma Z_fact_simpl : forall n : nat,
  Z_fact (S n) = Z.of_nat (S n) * Z_fact n.
Proof.
  intro n. simpl. reflexivity.
Qed.

Lemma Z_fact_eq_fact : forall n : nat,
  Z_fact n = Z.of_nat (fact n).
Proof.
  induction n as [| n IH]; try reflexivity.
  repeat rewrite Z_fact_simpl. rewrite IH. rewrite <- Nat2Z.inj_mul. reflexivity.
Qed.

Definition Z_choose (n k : nat) : Z :=
  if (n <? k)%nat then 0 else
  Z_fact n / (Z_fact k * Z_fact (n - k)).

Lemma Z_choose_eq_choose : forall n k : nat,
  Z_choose n k = Z.of_nat (choose n k).
Proof.
  intros n k. unfold Z_choose, choose. destruct (n <? k)%nat; try reflexivity.
  rewrite Z_fact_eq_fact. rewrite Nat2Z.inj_div. rewrite Nat2Z.inj_mul.
  repeat rewrite Z_fact_eq_fact. reflexivity.
Qed.

Fixpoint choose_3 (n k : nat) : nat :=
  match n, k with
  | 0%nat, 0%nat => 1
  | 0%nat, _ => 0
  | _, 0%nat => 1
  | S n', S k' => choose_3 n' k' + choose_3 n' k
  end.  

Open Scope nat_scope.

Lemma choose_3_eq_choose : forall n k : nat,
  choose_3 n k = choose n k.
Proof.
  induction n as [| n IH]; destruct k as [| k]; try reflexivity.
  simpl. rewrite n_choose_0. reflexivity. simpl. rewrite IH. rewrite IH. 
  rewrite binomial_recursion_4 with (n := S n) (k := S k); try lia.
  replace (S n - 1) with n by lia. replace (S k - 1) with k by lia. reflexivity.
Qed.