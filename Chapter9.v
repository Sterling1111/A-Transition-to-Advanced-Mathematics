Require Import Imports QRT.
Require Export Chapter8.

Open Scope Z_scope.

Lemma lemma_9_2_a : forall x : Z,
  Z.Even (3*x + 1) -> Z.Odd (5*x + 2).
Proof.
  intros x H1. apply odd_plus_Z. right. split.
  - apply odd_mult_Z.
    -- exists 2. lia.
    -- apply even_plus_Z in H1 as [[H1 [k H2]] | [[k H1] H2]]; try lia. pose proof Z.Even_or_Odd x as [[j H3] | H3]; auto; lia.
  - exists 1. lia.
Qed.

Lemma lemma_9_2_b : forall x : Z,
  Z.Even (3*x + 1) -> Z.Odd (5*x + 2).
Proof.
  intros x. apply contra_2_reverse. intros H1. apply not_odd_iff_even_Z in H1. apply not_even_iff_odd_Z.
  apply even_plus_Z in H1 as [[H1 _] | [_ [k H2]]]; try lia. apply even_mult_Z in H1 as [[k H1] | H1]; try lia.
  apply odd_plus_Z; left. split; try (exists 0; lia). apply even_mult_Z; auto.
Qed.

Lemma lemma_9_2_c : forall x : Z,
  Z.Even (3*x + 1) -> Z.Odd (5*x + 2).
Proof.
  intros x. apply or_to_imply. apply NNPP. intros H1.
  apply not_or_and in H1 as [H1 H2]. apply NNPP in H1. apply not_odd_iff_even_Z in H2 as H2.
  apply even_plus_Z in H1 as [[_ [k H3]] | [H1 H3]]; try lia. apply odd_mult_Z with (x := 3) in H1.
  2 : { exists 1. lia. } apply even_plus_Z in H2 as [[H2 _]| [_ [k H2]]]; try lia. 
  apply even_mult_Z in H2 as [[k H2] | H2]; try lia. apply Z.Even_Odd_False with (x := x); auto.
Qed.

Lemma lemma_9_3_helper_1 : forall a : Z,
  Z.Even (a^2) -> Z.Even a.
Proof.
  intros a. apply contra_2_reverse. intros H1. apply not_even_iff_odd_Z in H1.
  apply not_even_iff_odd_Z. replace (a^2) with (a * a) by lia. apply odd_mult_Z; auto.
Qed.

Lemma lemma_9_3_helper_2 : forall a b : Z,
  Z.Odd a -> Z.Odd b -> ~(4 | a^2 + b^2).
Proof.
  intros a b [i H1] [j H2] [k H4]; lia.
Qed.

Lemma lemma_9_3 : forall a b c : Z,
  a^2 + b^2 = c^2 -> Z.Even a \/ Z.Even b.
Proof.
  intros a b c. apply or_to_imply. apply NNPP. intros H1.
  apply not_or_and in H1 as [H1 H2]. apply not_or_and in H2 as [H2 H3]. apply NNPP in H1.
  apply not_even_iff_odd_Z in H2. apply not_even_iff_odd_Z in H3. 
  assert (Z.Even (a^2 + b^2)) as H4. 
  {
    apply even_plus_Z. right. replace (a^2) with (a * a) by lia.
    replace (b^2) with (b * b) by lia. split; apply odd_mult_Z; auto. 
  }
  assert (Z.Even (c^2)) as H5. { rewrite <- H1; auto. }
  assert (Z.Even c) as [k H6]. { apply lemma_9_3_helper_1 in H5; auto. }
  replace (c^2) with (4 * k^2) in H1 by lia. pose proof (lemma_9_3_helper_2 a b H2 H3) as H7.
  apply H7. exists (k^2). lia.
Qed.

Definition rational (r : R) : Prop :=
  exists z1 z2 : Z, (r = (IZR z1) / (IZR z2))%R.

Definition irrational (r : R) : Prop :=
  ~ rational r.

Lemma gcd_0 : forall a b : Z, Z.gcd a b = 0 -> a = 0 /\ b = 0.
Proof.
  intros a b H1. split.
  - pose proof Z.gcd_divide_l a b as H2. destruct H2 as [k H2]. lia.
  - pose proof Z.gcd_divide_r a b as H2. destruct H2 as [k H2]. lia.
Qed.

Lemma gcd_gt_0 : forall a b : Z, a <> 0 -> b <> 0 -> Z.gcd a b > 0.
Proof.
  intros a b H1 H2. pose proof Z.gcd_nonneg a b. assert (Z.gcd a b = 0 \/ Z.gcd a b > 0) as [H3 | H3] by lia.
  - apply gcd_0 in H3. lia.
  - auto.
Qed.

Lemma rational_representation : forall r z1 z2,
  z1 <> 0 -> z2 <> 0 ->
  (r = IZR z1 / IZR z2)%R -> exists z1' z2',
    ((r = IZR z1' / IZR z2')%R /\ (forall x, x > 1 -> ~(x | z1') \/ ~(x | z2'))).
Proof.
  intros r z1 z2 H1 H2 H3. exists (z1 / Z.gcd z1 z2). exists (z2 / Z.gcd z1 z2). split.
  - rewrite H3. pose proof Z.gcd_divide_r z1 z2 as H4. pose proof Z.gcd_divide_l z1 z2 as H5.
    unfold Z.divide in H4. unfold Z.divide in H5. destruct H4 as [k1 H4]. destruct H5 as [k2 H5].
    assert (Z.gcd z1 z2 <> 0) as H6 by lia.
    assert (H7 : Z.gcd z1 z2 > 0). { pose proof Z.gcd_nonneg z1 z2. lia. }
    replace (z1 / Z.gcd z1 z2) with (k2). 2 : { rewrite H5 at 1. rewrite Z_div_mult. reflexivity. lia. }
    replace (z2 / Z.gcd z1 z2) with (k1). 2 : { rewrite H4 at 1. rewrite Z_div_mult. reflexivity. lia. }
    rewrite H4. rewrite H5 at 1. repeat rewrite mult_IZR.
    replace ((IZR k2 * IZR (Z.gcd z1 z2) / (IZR k1 * IZR (Z.gcd z1 z2)))%R) with
            ( IZR k2 / IZR k1 * (IZR (Z.gcd z1 z2) / IZR (Z.gcd z1 z2)))%R.
    2 : { field. split. apply not_0_IZR. auto. apply not_0_IZR. lia. }
    rewrite Rdiv_diag. 2 : { apply not_0_IZR. lia. } nra.
  - intros x H4. apply not_and_or. intros [[a H5] [b H6]]. pose proof Z.gcd_divide_l z1 z2 as [c H7].
    pose proof Z.gcd_divide_r z1 z2 as [d H8]. rewrite H7 in H5 at 1. rewrite H8 in H6 at 1.
    rewrite Z_div_mult in H5 by (apply gcd_gt_0; auto). rewrite Z_div_mult in H6 by (apply gcd_gt_0; auto).
    rewrite H5 in H7. rewrite H6 in H8. assert (H9 : Z.divide (x * Z.gcd z1 z2) z1). { rewrite H7 at 2. exists (a). lia. }
    assert (H10 : Z.divide (x * Z.gcd z1 z2) z2). { exists (b). lia. } pose proof Z.gcd_greatest z1 z2 (x * Z.gcd z1 z2) as H11.
    apply H11 in H9. 2 : { auto. } unfold Z.divide in H9. destruct H9 as [k H9]. assert (Z.gcd z1 z2 > 0) as H12 by (apply gcd_gt_0; auto).
    assert (k < 0 \/ k = 0 \/ k > 0) as [H13 | [H13 | H13]] by lia.
    -- nia.
    -- nia.
    -- assert (H14 : k * x * Z.gcd z1 z2 > Z.gcd z1 z2). { rewrite <- Zmult_1_l. apply Zmult_gt_compat_r. lia. lia. }
       nia.
Qed.

Lemma even_pow2 : forall z,
  Z.Even (z * z) -> Z.Even z.
Proof.
  intros z H. pose proof Z.Even_or_Odd z as [H1 | H1].
  - auto.
  - destruct H1 as [k H1]. destruct H as [k' H]. nia.
Qed.

Lemma sqrt_rational_neq_0 : forall r z1 z2,
  (r > 0)%R -> sqrt r = (IZR z1 / IZR z2)%R -> (z1 <> 0 /\ z2 <> 0).
Proof.
  intros r z1 z2 H1 H2. split.
  - intros H3. rewrite H3 in H2. rewrite Rdiv_0_l in H2. pose proof sqrt_lt_R0 r. nra.
  - intros H3. rewrite H3 in H2. rewrite Rdiv_0_r in H2. pose proof sqrt_lt_R0 r. nra.
Qed.

Lemma sqrt_2_irrational : irrational (sqrt 2).
Proof.
  unfold irrational. unfold rational. unfold not. intros [z1 [z2 H1]].
  assert (z1 <> 0 /\ z2 <> 0) as [H2 H3] by (apply sqrt_rational_neq_0 with (r := 2%R); lra).
  assert (H4 : exists z1' z2', ((sqrt 2 = IZR z1' / IZR z2')%R /\ (forall x, x > 1 -> ~(x | z1') \/ ~(x | z2')))).
  { apply rational_representation with (z1 := z1) (z2 := z2). apply H2. apply H3. apply H1. }
  destruct H4 as [z1' [z2' [H4 H5]]]. assert (H6 : (sqrt 2 * sqrt 2 = (IZR z1' / IZR z2') * (IZR z1' / IZR z2'))%R) by nra.
  rewrite sqrt_sqrt in H6. 2 : { lra. } assert (H7 : (z1' <> 0 /\ z2' <> 0)) by (apply sqrt_rational_neq_0 with (r := 2%R); lra).
  destruct H7 as [H7 H8]. assert (H9 : (IZR z1' <> 0)%R) by (apply not_0_IZR; auto). assert (H10 : (IZR z2' <> 0)%R) by (apply not_0_IZR; auto).
  replace (IZR z1' / IZR z2' * (IZR z1' / IZR z2'))%R with ((IZR z1')^2 / (IZR z2')^2)%R in H6.
  2 : { field. auto. } apply Rmult_eq_compat_r with (r := ((IZR z2')^2)%R) in H6.
  replace ((IZR z1' ^ 2 / IZR z2' ^ 2 * IZR z2' ^ 2)%R) with ((IZR z1')^2)%R in H6.
  2 : { field. auto. } simpl in H6. repeat rewrite Rmult_1_r in H6. repeat rewrite <- mult_IZR in H6.
  apply eq_IZR in H6. assert (H11 : Z.Even (z1' * z1')). { exists (z2' * z2'). lia. }
  apply even_pow2 in H11. destruct H11 as [k1 H11]. assert (H12 : Z.Even (z2' * z2')). { exists (k1 * k1). nia. }
  apply even_pow2 in H12. destruct H12 as [k2 H12]. specialize (H5 2). destruct H5 as [H5 | H5].
  { lia. } { apply H5. unfold Z.divide. exists (k1). lia. } { apply H5. unfold Z.divide. exists (k2). lia. }
Qed.

Lemma ksqr_div_3_k_div_3 : forall k,
  Z.divide 3 (k^2) -> Z.divide 3 k.
Proof.
  intros k [a H1]. unfold Z.divide.
  assert (exists p, k = 3*p \/ k = 3*p+1 \/ k = 3*p+2) as [p H2] by zforms.
  exists p.  destruct H2. lia. destruct H. lia. lia.
Qed.

Lemma lemma_9_4 : irrational (sqrt 3).
unfold irrational. unfold rational. unfold not. intros [z1 [z2 H1]].
  assert (z1 <> 0 /\ z2 <> 0) as [H2 H3] by (apply sqrt_rational_neq_0 with (r := 3%R); lra).
  assert (H4 : exists z1' z2', ((sqrt 3 = IZR z1' / IZR z2')%R /\ (forall x, x > 1 -> ~(x | z1') \/ ~(x | z2')))).
  { apply rational_representation with (z1 := z1) (z2 := z2). apply H2. apply H3. apply H1. }
  destruct H4 as [z1' [z2' [H4 H5]]]. assert (H6 : (sqrt 3 * sqrt 3 = (IZR z1' / IZR z2') * (IZR z1' / IZR z2'))%R) by nra.
  rewrite sqrt_sqrt in H6. 2 : { lra. } assert (H7 : (z1' <> 0 /\ z2' <> 0)) by (apply sqrt_rational_neq_0 with (r := 3%R); lra).
  destruct H7 as [H7 H8]. assert (H9 : (IZR z1' <> 0)%R) by (apply not_0_IZR; auto). assert (H10 : (IZR z2' <> 0)%R) by (apply not_0_IZR; auto).
  replace (IZR z1' / IZR z2' * (IZR z1' / IZR z2'))%R with ((IZR z1')^2 / (IZR z2')^2)%R in H6.
  2 : { field. auto. } apply Rmult_eq_compat_r with (r := ((IZR z2')^2)%R) in H6.
  replace ((IZR z1' ^ 2 / IZR z2' ^ 2 * IZR z2' ^ 2)%R) with ((IZR z1')^2)%R in H6.
  2 : { field. auto. } simpl in H6. repeat rewrite Rmult_1_r in H6. repeat rewrite <- mult_IZR in H6. apply eq_IZR in H6.
  assert (Z.divide 3 (z1'^2)) as H11 by (exists (z2' * z2'); lia). assert (Z.divide 3 z1') as H12 by (apply ksqr_div_3_k_div_3; auto).
  pose proof H11 as [p H13]. pose proof H12 as [q H14]. replace (z1'^2) with (z1' * z1') in H13 by lia.
  assert (H15 : z1' * z1' = 3 * (3 * q * q)) by lia. rewrite H15 in H6. assert (Z.divide 3 (z2'^2)) as H16 by (exists (q * q); lia).
  assert (Z.divide 3 z2') as H17 by (apply ksqr_div_3_k_div_3; auto). specialize (H5 3). destruct H5 as [H5 | H5].
  { lia. } { tauto. } { tauto. }
Qed.

Lemma kcub_even_k_even : forall k,
  Z.Even (k^3) -> Z.Even k.
Proof.
  intros k H1. pose proof Z.Even_or_Odd k as [H2 | H2].
  - auto.
  - destruct H2 as [k' H2]. assert (Z.Odd (k^3)) as H3.
    { exists (4*k'^3 + 6*k'^2 + 3*k'). nia. } rewrite <- Zodd_equiv in H3.
    rewrite <- Zeven_equiv in H1. apply Zodd_not_Zeven in H3. tauto.
Qed.

Lemma lemma_9_5 : irrational (Rpower 2 (1/3)).
Proof.
  unfold irrational. unfold rational. unfold not. intros [z1 [z2 H1]].
  assert (H2 : Rpower 2 (1/3) <> 0%R). 
  { assert (H3 : (Rpower 2 0 < Rpower 2 (1/3))%R) by (apply Rpower_lt; lra). rewrite Rpower_O in H3; lra. }
  assert (z1 <> 0 /\ z2 <> 0) as [H3 H4].
  { assert (z1 = 0 \/ z2 = 0 \/ z1 <> 0 /\ z2 <> 0) as [H3 | [H3 | H3]] by lia; auto; rewrite H3 in H1; try rewrite Rdiv_0_l in H1; try rewrite Rdiv_0_r in H1; lra. }
  assert (H5 : exists z1' z2', ((Rpower 2 (1/3) = IZR z1' / IZR z2')%R /\ (forall x, x > 1 -> ~(x | z1') \/ ~(x | z2')))).
  { apply rational_representation with (z1 := z1) (z2 := z2). apply H3. apply H4. apply H1. }
  destruct H5 as [z1' [z2' [H5 H6]]]. assert (H7 : (Rpower 2 (1/3) * Rpower 2 (1/3) * Rpower 2 (1/3) = (IZR z1' / IZR z2') * (IZR z1' / IZR z2') * (IZR z1' / IZR z2'))%R) by nra.
  assert (H8 : z1' <> 0 /\ z2' <> 0).
  { assert (z1' = 0 \/ z2' = 0 \/ z1' <> 0 /\ z2' <> 0) as [H8 | [H8 | H8]] by lia; auto; rewrite H8 in H5; try rewrite Rdiv_0_l in H5; try rewrite Rdiv_0_r in H5; lra. }
  replace (Rpower 2 (1/3) * Rpower 2 (1/3) * Rpower 2 (1/3))%R with 2%R in H7.
  2 : { repeat rewrite <- Rpower_plus. replace (1/3 + 1/3 + 1/3)%R with 1%R by lra. rewrite Rpower_1;lra. }
  replace (IZR z1' / IZR z2' * (IZR z1' / IZR z2') * (IZR z1' / IZR z2'))%R with ((IZR z1')^3 / (IZR z2')^3)%R in H7 by (field; apply not_0_IZR; tauto).
    apply Rmult_eq_compat_r with (r := ((IZR z2')^3)%R) in H7. replace ((IZR z1' ^ 3 / IZR z2' ^ 3 * IZR z2' ^ 3)%R) with ((IZR z1')^3)%R in H7 by (field; apply not_0_IZR; tauto).
  replace 3 % nat with (Z.to_nat 3) in H7 at 1 by auto.
  assert (Z.Even (z1'^3)) as H9. 
  { replace 3 with (Z.of_nat 3) by auto. exists (z2'^3). apply eq_IZR. rewrite <- pow_IZR. rewrite mult_IZR. 
    apply eq_sym. rewrite pow_IZR in H7. replace (Z.of_nat (Z.to_nat 3)) with (3) in H7 by lia. apply H7. }
  assert (H10 : Z.Even z1'). { apply kcub_even_k_even in H9. auto. }
  assert (H11 : (2 | z1')). { destruct H10 as [k H10]. exists (k). lia. }
  destruct H10 as [k H10]. rewrite H10 in H7. assert (H12 : (IZR z2' ^ 3 = 4 * IZR (k^3))%R).
  { replace 3%nat with (Z.to_nat 3) in H7 by auto. rewrite pow_IZR with (z := 2 * k) in H7. replace (Z.to_nat 3) with 3%nat in H7 by auto.
    replace (Z.of_nat 3) with 3 in H7 by auto. replace ((2 * k) ^ 3) with (8 * k^3) in H7 by lia. rewrite mult_IZR in H7. nra. }
  assert (Z.Even (z2'^3)) as H13. 
  { replace 3 with (Z.of_nat 3) by auto. exists (2 * k^3). apply eq_IZR. rewrite <- pow_IZR. rewrite mult_IZR. 
    rewrite mult_IZR. replace (2 * (2 * IZR (k^3)))%R with (4 * IZR (k^3))%R by lra. nra. }
  assert (H14 : Z.Even z2'). { apply kcub_even_k_even in H13. auto. }
  assert (H15 : (2 | z2')). { destruct H14 as [k' H14]. exists (k'). lia. }
  specialize (H6 2) as [H6 | H6]; try lia; tauto.
Qed.

Lemma lemma_9_6 : forall x y, rational x -> irrational y -> irrational (x + y).
Proof.
    intros x y [z1 [z2 H1]] H2 [z3 [z4 H3]]. apply H2. 
    assert ((x = 0 \/ y = 0 \/ x <> 0 /\ y <> 0)%R) as [H4 | [H4 | H4]] by lra.
    - exists z3, z4. nra.
    - exists 0, 0. nra.
    - assert (x + y = 0 \/ x + y <> 0)%R as [H5 | H5] by lra.
      -- exists (-z1), z2. assert (y = -x)%R as H6 by nra. rewrite H1 in H6. rewrite H6. rewrite opp_IZR. nra.
      -- exists (z3 * z2 - z1 * z4), (z2 * z4).
         assert (H6 : forall a b c, (a <> 0 /\ a = IZR b / IZR c)%R -> c <> 0).
        { intros a b c [H6 H7]. assert (c <> 0 \/ c = 0) as [H8 | H8] by lia. auto. rewrite H8 in H7. rewrite Rdiv_0_r in H7. nra. }
        assert (H7 : z2 <> 0 /\ z4 <> 0). { split. apply H6 with (a := x) (b := z1); tauto. apply H6 with (a := (x + y)%R) (b := z3). tauto.  }
      rewrite minus_IZR. repeat rewrite mult_IZR. assert (y = IZR z3 / IZR z4 - x)%R as H8. { nra. } rewrite H1 in H8. rewrite H8. field.
      split; (apply not_0_IZR; lia).
Qed.

Lemma irrational_neg : forall x,
  irrational x -> irrational (-x).
Proof.
  intros x H1 [z1 [z2 H2]]. apply H1. exists (-z1), z2. rewrite opp_IZR. nra.
Qed.

Lemma irrational_sub : forall x y,
  ((irrational x /\ rational y) \/ (rational x /\ irrational y)) -> irrational (x - y).
Proof.
  intros x y. intros [[H1 [z1 [ z2 H2]]] | [[z1 [ z2 H1]] H2]] [z3 [z4 H3]].
  - assert (z2 = 0 \/ z2 <> 0) as [H4 | H4]; assert (z4 = 0 \/ z4 <> 0) as [H5 | H5]; try lia.
    -- subst. unfold Rdiv in H3. rewrite Rinv_0 in H3. assert (x = 0)%R by nra. assert (rational x) by (exists 0, 1; nra). apply H1. auto.
    -- subst. unfold Rdiv in H3. rewrite Rinv_0 in H3. assert (x = IZR z3 / IZR z4)%R by nra. apply H1. exists z3, z4. auto.
    -- subst. unfold Rdiv in H3. rewrite Rinv_0 in H3. assert (x = IZR z1 / IZR z2)%R by nra. apply H1. exists z1, z2. auto.
    -- apply H1. exists (z1 * z4 + z2 * z3), (z2 * z4). rewrite plus_IZR. repeat rewrite mult_IZR. apply Rplus_eq_compat_r with (r := y) in H3.
       replace (x - y + y)%R with x in H3 by lra. rewrite H2 in H3. rewrite H3. field; split. apply not_0_IZR. lia. apply not_0_IZR. lia.
  - assert (z2 = 0 \/ z2 <> 0) as [H4 | H4]; assert (z4 = 0 \/ z4 <> 0) as [H5 | H5]; try lia.
    -- subst. unfold Rdiv in H3. rewrite Rinv_0 in H3. assert (y = 0)%R by nra. assert (rational y) by (exists 0, 1; nra). apply H2. auto.
    -- subst. unfold Rdiv in H3. rewrite Rinv_0 in H3. assert (y = - IZR z3 / IZR z4)%R by nra. apply H2. exists (-z3), z4. rewrite opp_IZR. auto.
    -- subst. unfold Rdiv in H3. rewrite Rinv_0 in H3. assert (y = IZR z1 / IZR z2)%R by nra. apply H2. exists z1, z2. auto.
    -- apply H2. exists (z1 * z4 - z2 * z3), (z2 * z4). rewrite minus_IZR. repeat rewrite mult_IZR. assert (y = x - (IZR z3 / IZR z4))%R as H6 by nra.
       rewrite H6. rewrite H1. field. split. apply not_0_IZR. lia. apply not_0_IZR. lia.
Qed.

Lemma x_neq_0_IZR_den_neq_0 : forall x y z,
  (x <> 0 /\ x = IZR y / IZR z)%R -> z <> 0. 
Proof.
  intros x y z [H1 H2]. assert (z <> 0 \/ z = 0) as [H3 | H3] by lia. auto. rewrite H3 in H2. rewrite Rdiv_0_r in H2. nra.
Qed.

Lemma x_neq_0_IZR_num_neq_0 : forall x y z,
  (x <> 0 /\ x = IZR y / IZR z)%R -> y <> 0.
Proof.
  intros x y z [H1 H2]. assert (y <> 0 \/ y = 0) as [H3 | H3] by lia. auto. rewrite H3 in H2. rewrite Rdiv_0_l in H2. nra.
Qed.

Lemma mult_rational : forall a b,
  rational a -> rational b -> rational (a * b).
Proof.
  intros a b [z1 [z2 H1]] [z3 [z4 H2]].
  assert (a = 0 \/ b = 0 \/ a <> 0 /\ b <> 0)%R as [H3 | [H3 | [H3 H4]]] by lra.
  - exists 0, 1. nra.
  - exists 0, 1. nra.
  - exists (z1 * z3). exists (z2 * z4). rewrite H1. rewrite H2. repeat rewrite mult_IZR. field.
    split; apply not_0_IZR.
    -- apply x_neq_0_IZR_den_neq_0 with (x := b) (y := z3) (z := z4). auto.
    -- apply x_neq_0_IZR_den_neq_0 with (x := a) (y := z1) (z := z2). auto.
Qed.

Lemma lemma_9_7 : forall a b,
  a <> 0%R -> rational a -> irrational b -> irrational (a * b).
Proof.
  intros a b H1 H2 H3. assert (irrational (a * b) \/ rational (a * b)) as [H4 | H4].
  { unfold irrational. tauto. } auto.
  destruct H2 as [z1 [z2 H2]]. assert (H5 : z1 <> 0). { apply x_neq_0_IZR_num_neq_0 with (x := a) (y := z1) (z := z2). auto. }
  assert (H6 : z2 <> 0). { apply x_neq_0_IZR_den_neq_0 with (x := a) (y := z1) (z := z2). auto. }
  assert (H7 : rational (/ a)) by (exists z2, z1; rewrite H2; field; split; apply not_0_IZR; lia).
  assert (H8 : b <> 0%R) by (intros H8; apply H3; exists 0, 1; nra).
  assert (H9 : (/ a <> 0)%R) by (apply Rinv_neq_0_compat; auto).
  assert (H10 : rational b).
  { replace b with (a * b / a)%R by (field; auto). apply mult_rational; auto. }
  unfold irrational in H3. tauto.
Qed.

Lemma Rdiv_eq_0 : forall a b,
  (a / b = 0)%R -> (a = 0 \/ b = 0)%R.
Proof.
  intros a b H1. assert (a = 0 \/ a <> 0)%R as [H2 | H2] by lra; assert (b = 0 \/ b <> 0)%R as [H3 | H3] by lra; try nra.
  apply Rmult_eq_compat_r with (r := b) in H1. field_simplify in H1; nra.
Qed.

Lemma irrational_div : forall a b,
  (a <> 0)%R -> (b <> 0)%R -> ((irrational a /\ rational b) \/ (rational a /\ irrational b)) -> irrational (a / b).
Proof.
  intros a b H1 H2 [[H3 [z1 [z2 H4]]] | [[z1 [z2 H3]] H4]] [z3 [z4 H5]].
  - assert (z1 = 0 \/ z1 <> 0) as [H6 | H6]; assert (z2 = 0 \/ z2 <> 0) as [H7 | H7];
    assert (z3 = 0 \/ z3 <> 0) as [H8 | H8]; assert (z4 = 0 \/ z4 <> 0) as [H9 | H9]; try lia; subst; try lra; try (unfold Rdiv in H2; rewrite Rinv_0 in H2; lra).
    -- replace (0 / 0)%R with 0%R in H5 by lra. apply Rdiv_eq_0 in H5. tauto.
    -- replace (0 / IZR z4)%R with 0%R in H5 by lra. apply Rdiv_eq_0 in H5. tauto.
    -- replace (IZR z3 / 0)%R with 0%R in H5. 2 : { unfold Rdiv; rewrite Rinv_0; lra. } apply Rdiv_eq_0 in H5. tauto.
    -- apply H3. exists (z1 * z3), (z2 * z4). repeat rewrite mult_IZR. assert (IZR z1 <> 0 /\ IZR z2 <> 0 /\ IZR z3 <> 0 /\ IZR z4 <> 0)%R as [H10 [H11 [ H12 H13]]] by (repeat split; apply not_0_IZR; lia).
       apply Rmult_eq_compat_r with (r := (IZR z1 / IZR z2)%R) in H5. field_simplify in H5; try nra.
  - assert (z1 = 0 \/ z1 <> 0) as [H6 | H6]; assert (z2 = 0 \/ z2 <> 0) as [H7 | H7];
    assert (z3 = 0 \/ z3 <> 0) as [H8 | H8]; assert (z4 = 0 \/ z4 <> 0) as [H9 | H9]; try lia; subst; try lra; try (unfold Rdiv in H1; rewrite Rinv_0 in H1; lra).
    -- replace (0 / 0)%R with 0%R in H5 by lra. apply Rdiv_eq_0 in H5. tauto.
    -- replace (0 / IZR z4)%R with 0%R in H5 by lra. apply Rdiv_eq_0 in H5. tauto.
    -- replace (IZR z3 / 0)%R with 0%R in H5. 2 : { unfold Rdiv; rewrite Rinv_0; lra. } apply Rdiv_eq_0 in H5. tauto.
    -- apply H4. exists (z1 * z4), (z2 * z3). repeat rewrite mult_IZR. assert (IZR z1 <> 0 /\ IZR z2 <> 0 /\ IZR z3 <> 0 /\ IZR z4 <> 0)%R as [H10 [H11 [ H12 H13]]] by (repeat split; apply not_0_IZR; lia).
       apply Rmult_eq_compat_r with (r := b) in H5. field_simplify in H5; try nra. apply Rmult_eq_compat_r with (r := (IZR z4 / IZR z3)%R) in H5. field_simplify in H5; try nra.
Qed.

Lemma lemma_9_8 : forall a : R,
  (a > 0)%R -> irrational a -> exists b, (b > 0)%R /\ irrational b /\ (b < a)%R.
Proof.
  intros a H1 H2. exists ((1 / 2) * a)%R. repeat split; try lra.
  apply lemma_9_7; auto; try lra. exists 1, 2. nra.
Qed.

Lemma lemma_9_9 : forall x y : Z,
  33 * x + 132 * y <> 57.
Proof.
  intros x y H1. replace (33 * x + 132 * y) with (33 * (x + 4 * y)) in H1 by lia.
  (*just go through some possibilities. let z = x + 4 * y. if z = 0, 1 too small. forall the rest too big. FAIL*)
  lia. (* thanks lia! *)
Qed.