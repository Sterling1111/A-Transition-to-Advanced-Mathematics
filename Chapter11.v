Require Import Imports Reals_util.
Require Export Chapter10.

Open Scope Z_scope.

Lemma lemma_11_1_a : exists a b : R,
    rational a /\ rational b /\ rational (Rpower a b).
Proof.
    exists 1%R, 1%R; repeat split; exists 1, 1; try lra. rewrite Rpower_1; lra.
Qed.

Lemma lemma_11_1_b : exists a b : R,
    rational a /\ rational b /\ irrational (Rpower a b).
Proof.
    exists 2%R, (/2)%R; repeat split.
    - exists 2, 1; lra.
    - exists 1, 2; lra.
    - intros H1. rewrite Rpower_sqrt in H1; try lra. apply sqrt_2_irrational; auto.
Qed.

Lemma Rpower_gt_0 : forall r n,
  (r > 0)%R -> (Rpower r n > 0)%R.
Proof.
  intros r n H1. unfold Rpower. destruct (Rle_dec 0 r).
  - apply exp_pos.
  - apply exp_pos.
Qed.

Lemma lemma_11_1_c : exists a b : R,
    irrational a /\ irrational b /\ irrational (Rpower a b).
Proof.
    assert (irrational (Rpower (sqrt 2) (sqrt 2)) \/ rational (Rpower (sqrt 2) (sqrt 2))) as [H1 | H1] by (tauto).
    - exists (sqrt 2), (sqrt 2)%R. repeat split; try (apply sqrt_2_irrational; auto); auto.
    - exists (sqrt 2), (1 - sqrt 2)%R. repeat split; try (apply sqrt_2_irrational; auto). apply irrational_sub. right. split. exists 1, 1; lra. apply sqrt_2_irrational; auto.
    assert (Rpower (sqrt 2) (sqrt 2) * Rpower (sqrt 2) (1 - sqrt 2) = Rpower (sqrt 2) 1)%R as H2.
    { rewrite <- Rpower_plus. replace (sqrt 2 + (1 - sqrt 2))%R with 1%R by lra. reflexivity. }
    rewrite Rpower_1 in H2. 2 : { apply sqrt_lt_R0; lra. } intros H3.
    assert (rational (sqrt 2)) as H4. { rewrite <- H2. apply mult_rational; auto. } exfalso. apply (sqrt_2_irrational H4).
Qed. 

Lemma Rpower_1_base : forall r, Rpower 1 r = 1%R.
Proof.
    intros r. unfold Rpower. destruct (Rle_dec 0 1).
    - rewrite ln_1. rewrite Rmult_0_r. rewrite exp_0. lra.
    - lra.
Qed.

Lemma lemma_11_1_d : exists a b : R,
    rational a /\ irrational b /\ rational (Rpower a b).
Proof.
    exists 1%R, (sqrt 2)%R; repeat split. try (exists 1, 1; lra).
    - apply sqrt_2_irrational.
    - rewrite Rpower_1_base. exists 1, 1; lra.
Qed.

Lemma lemma_11_1_e : exists a b : R,
    rational a /\ irrational b /\ irrational (Rpower a b).
Proof.
    assert (irrational (Rpower 2 (sqrt 2)) \/ rational (Rpower 2 (sqrt 2))) as [H1 | H1] by (tauto).
    - exists 2%R, (sqrt 2)%R; repeat split; try (exists 2, 1; lra); auto. apply sqrt_2_irrational; auto.
    - exists 2%R, (/2 - sqrt 2)%R. repeat split. exists 2, 1; lra. apply irrational_sub. right. split. exists 1, 2; lra. apply sqrt_2_irrational; auto.
    intros H2.
      assert (Rpower 2 (sqrt 2) * Rpower 2 (/2 - sqrt 2) = Rpower (sqrt 2) 1)%R as H3.
      { rewrite <- Rpower_plus. replace (sqrt 2 + (/2 - sqrt 2))%R with (/2)%R by lra. rewrite Rpower_1. 2 : { apply sqrt_lt_R0; lra. } rewrite Rpower_sqrt; lra. }
      rewrite Rpower_1 in H3. 2 : { apply sqrt_lt_R0; lra. }
      assert (rational (sqrt 2)) as H4. { rewrite <- H3. apply mult_rational; auto. } exfalso. apply (sqrt_2_irrational H4).
Qed.

Lemma lemma_11_1_f : exists a b : R,
    irrational a /\ rational b /\ rational (Rpower a b).
Proof.
    exists (sqrt 2)%R, 2%R; repeat split.
    - apply sqrt_2_irrational.
    - exists 2, 1; lra.
    - exists 2, 1. replace 2%R with (INR 2) by reflexivity. rewrite Rpower_pow. rewrite pow2_sqrt. lra. simpl. lra. simpl. apply sqrt_lt_R0; lra.
Qed.

Lemma lemma_11_1_g : exists a b : R,
    irrational a /\ rational b /\ irrational (Rpower a b).
Proof.
    exists (sqrt 2)%R, 1%R. repeat split.
    - apply sqrt_2_irrational.
    - exists 1, 1; lra.
    - replace 1%R with (INR 1) by reflexivity.  rewrite Rpower_pow. simpl. rewrite Rmult_1_r. apply sqrt_2_irrational.
      apply sqrt_lt_R0; lra.
Qed.

Lemma lemma_11_2 : forall x y,
  x <> 0%R -> rational x -> irrational y -> irrational (x * y).
Proof.
  intros x y H1 H2 H3. assert (irrational (x * y) \/ rational (x * y)) as [H4 | H4].
  { unfold irrational. tauto. } auto.
  destruct H2 as [z1 [z2 H2]]. assert (H5 : z1 <> 0). { apply x_neq_0_IZR_num_neq_0 with (x := x) (y := z1) (z := z2). auto. }
  assert (H6 : z2 <> 0). { apply x_neq_0_IZR_den_neq_0 with (x := x) (y := z1) (z := z2). auto. }
  assert (H7 : rational (/ x)) by (exists z2, z1; rewrite H2; field; split; apply not_0_IZR; lia).
  assert (H8 : y <> 0%R) by (intros H8; apply H3; exists 0, 1; nra).
  assert (H9 : (/ x <> 0)%R) by (apply Rinv_neq_0_compat; auto).
  assert (H10 : rational y).
  { replace y with (x * y / x)%R by (field; auto). apply mult_rational; auto. }
  unfold irrational in H3. tauto.
Qed.

Lemma lemma_11_2' : 
    (forall x y, rational x -> irrational y -> irrational (x * y))-> False.
Proof.
    intros H1. specialize (H1 0%R (sqrt 2)%R). apply H1.
    - exists 0, 1; lra.
    - apply sqrt_2_irrational.
    - exists 0, 1; lra.
Qed.

Lemma lemma_11_3 : 
    (forall s, Z.Odd (6 * s - 3) -> Z.Odd s) -> False.
Proof.
    intros H1. specialize (H1 0). simpl in H1. assert (Z.Odd (-3)) as H2 by (exists (-2); lia).
    specialize (H1 H2). destruct H1 as [k H1]. lia.
Qed.

Lemma lemma_11_4 :
    (exists x, Z.Odd (x^2 + x)) -> False.
Proof.
    apply contra_2_reverse. intros _. apply all_not_not_ex.
    intros x H1. pose proof (Z.Even_or_Odd x) as [H2 | H2].
    - apply odd_plus_Z in H1 as [[H1 H3] | [H1 _]].
      -- apply Z.Even_Odd_False with (x := x); auto.
      -- replace (x^2) with (x * x) in H1 by lia. assert (Z.Even (x * x)).
         { apply even_mult_Z; auto. } apply Z.Even_Odd_False with (x := x * x); auto.
    - apply odd_plus_Z in H1 as [[H1 _] | [H1 H3]].
      -- replace (x^2) with (x * x) in H1 by lia. apply even_mult_Z in H1 as [H1 | H1]; (apply Z.Even_Odd_False with (x := x); auto).
      -- apply Z.Even_Odd_False with (x := x); auto.
Qed.

Open Scope R_scope.

Lemma lemma_11_5 : forall a,
    a > 0 -> rational a -> exists x, irrational x /\ (0 < x < a)%R.
Proof.
    intros a H1 H2. exists (a / sqrt 2)%R. split.
    - apply irrational_div; try lra.
      -- assert (0 < sqrt 2)%R by (apply sqrt_lt_R0; lra). lra.
      -- right. split; auto. apply sqrt_2_irrational.
    - split.
      -- assert (sqrt 2 > 0)%R by (apply sqrt_lt_R0; lra). apply Rdiv_pos_pos; auto.
      -- assert (sqrt 2 > 1)%R as H3. { apply sqrt_2_gt_1. } apply Rmult_lt_reg_r with (r := sqrt 2).
         apply sqrt_lt_R0; lra. field_simplify. nra. nra.
Qed.

Lemma exists_integer_between_R : forall x y,
    (x + 1 < y)%R -> exists z, (x < IZR z < y)%R.
Proof.
    intros x y H1. pose proof (classic (exists z, x = IZR z)) as [H2 | H2].
    - destruct H2 as [z1 H2]. exists (z1 + 1)%Z. split.
      -- rewrite H2. apply IZR_lt. lia.
      -- rewrite plus_IZR. rewrite <- H2. lra.
    - assert (forall z, x <> IZR z) as H3. { apply not_ex_not_all. intros [z H3]. apply H2. exists z. apply NNPP in H3. apply H3. }
      exists (up x). split.
      -- pose proof (archimed x) as [H4 H5]. apply H4.
      -- pose proof (archimed x) as [H4 H5]. lra.
Qed.

Lemma lemma_11_6 : forall x y,
    (x < y) -> exists z, rational z /\ x < z < y.
Proof.
    intros x y H1. set (z := 1 / (y - x)). assert (exists d, z < IZR d < z + 2) as [d [H2 H3]].
    { apply exists_integer_between_R. lra. } assert (IZR d * y - IZR d * x > 1)%R as H4.
    { 
        rewrite <- Rmult_minus_distr_l. apply Rmult_lt_reg_r with (r := / (y - x)). apply Rinv_pos.
        lra. field_simplify. fold z. apply H2. lra. lra.
    }
    assert (exists n, IZR d * x < IZR n < IZR d * y) as [n [H5 H6]].
    { apply exists_integer_between_R. lra. } exists (IZR n / IZR d)%R. split.
    - exists n, d. reflexivity.
    - assert (IZR d > 0) as H7 by nra. split; apply Rmult_lt_compat_r with (r := / IZR d) in H5, H6;
      field_simplify in H5; field_simplify in H6; try apply Rinv_pos; lra.
Qed.   
