Require Import ZArith Lia Classical Reals Lra Classical_sets List String
               Ensembles QArith ClassicalFacts Finite_sets Powerset Finite_sets_facts Image 
               NArith DecimalString DecimalNat DecimalNat Decimal
               Fibonacci Sums Sets Binomial QRT WI_SI_WO.

Require Export Chapter17.

Import ListNotations SetNotations Choose_Notations.

Open Scope string_scope.

Definition compute_extgcd_text (pair : Z * Z) : string :=
  let (a, b) := pair in
  let '(x, y, gcd) := Znumtheory.extgcd a b in
  let equation :=
    Z_to_string gcd ++ " = " ++
    Z_to_string a ++ " * " ++ Z_to_string x ++ " + " ++
    Z_to_string b ++ " * " ++ Z_to_string y in
  equation.

Compute map compute_extgcd_text [(15, 27); (29, 23); (91, 133); (221, 377)].

Close Scope string_scope.

Definition linear_combination (a b n : Z) : Prop :=
  exists x y : Z, n = a * x + b * y.

Theorem theorem_18_5 : forall a b n,
  (a <> 0 \/ b <> 0) -> n > 0 -> linear_combination a b n -> (Z.gcd a b <= n)%Z /\ linear_combination a b (Z.gcd a b).
Proof.
  intros a b n H1 H2 H3.
  set (S z := exists x y : Z, z = a * x + b * y /\ a * x + b * y > 0).
  assert (H4 : forall z, S z -> z >= 0).
  { intros z H4. unfold S in H4. destruct H4 as [x [y [H4 H5]]]. lia. }
  assert (H5 : exists z, S z).
  {
    pose proof (Z.lt_trichotomy a 0) as [H5 | [H5 | H5]]; pose proof (Z.lt_trichotomy b 0) as [H6 | [H6 | H6]]; subst; unfold S; try lia;
    first [exists a,1,0;split;lia | exists(-a),(-1),0;split;lia | exists b,0,1;split;lia | exists(-b),0,(-1);split;lia].
  }
  pose proof (well_ordering_Z S H4 H5) as [s [H6 H7]].
  destruct H6 as [x [y [H6 H8]]]. set (d := Z.gcd a b).
  pose proof gcd_satisfies_gcd_theory a b as H9. unfold gcd_theory in H9.
  assert ((a =? 0) && (b =? 0) = false) as H10 by lia.
  rewrite H10 in H9. clear H10. destruct H9 as [H9 [H10 H11]].
  assert (H12 : (d | (a * x + b * y))). { apply theorem_7_15; unfold d; auto. }
  assert (H13 : d <= s). { subst; apply Z.divide_pos_le; auto; lia. }
  pose proof quotient_remainder_theorem_existence a s ltac :(lia) as [q [r [H14 H15]]].
  assert (linear_combination a b r) as H16. { exists (1 - q * x), (-q*y). lia. }
  assert (r > 0 \/ r = 0) as [H17 | H17] by lia.
  - assert (S r) as H18. { destruct H16 as [x0 [y0 H16]]; exists x0, y0; split; lia. }
    specialize (H7 r ltac :(lia) H18). lia.
  - assert (s | a) as H18. { exists q. lia. }
    pose proof quotient_remainder_theorem_existence b s ltac:(lia) as [q0[r0 [H19 H20]]].
    assert (linear_combination a b r0) as H21. { exists (-q0 * x), (1 - q0 * y). nia. }
    assert (r0 > 0 \/ r0 = 0) as [H22 | H22] by lia.
    -- assert (S r0) as H23. { destruct H21 as [x0 [y0 H21]]; exists x0, y0; split; lia. }
       specialize (H7 r0 ltac:(lia) H23). lia.
    -- assert (s | b) as H23. { exists q0. lia. }
       assert (s <= d) as H26. { specialize (H11 s ltac:(auto)). auto. }
       replace d with s by lia. split. destruct H3 as [x2 [y2 H3]]. apply H7; try lia.
       exists x2, y2. lia. exists x, y; lia.
Qed.

Lemma exists_pos_linear_combination : forall a b, 
  (a <> 0 \/ b <> 0) -> exists n, n > 0 /\ linear_combination a b n.
Proof.
  intros a b H1. pose proof (Z.lt_trichotomy a 0) as [H2 | [H2 | H2]]; pose proof (Z.lt_trichotomy b 0) as [H3 | [H3 | H3]]; subst; try lia;
  first [ exists a; split; [lia | exists 1,0;lia] | 
          exists(-a); split; [lia | exists (-1),0;lia] |
          exists b; split; [lia | exists 0,1;lia ] | 
          exists(-b); split; [lia | exists 0,(-1); lia]].
Qed.

Lemma gcd_is_linear_combination : forall a b,
  linear_combination a b (Z.gcd a b).
Proof.
  intros a b. assert (a = 0 /\ b = 0 \/ a <> 0 \/ b <> 0) as [[H1 H2] | H1] by lia.
  - rewrite H1, H2. exists 0, 0. compute. lia.
  - pose proof exists_pos_linear_combination a b H1 as [n [H3 H4]].
    pose proof theorem_18_5 a b n H1 H3 H4 as [_ H5]. auto.
Qed.

Theorem theorem_18_10 : forall a b,
  Z.gcd a b = 1 <-> linear_combination a b 1. 
Proof.
  intros a b. split; intros H1.
  - rewrite <- H1. apply gcd_is_linear_combination.
  - assert (a = 0 /\ b = 0 \/ a <> 0 \/ b <> 0) as [H2 | H2] by lia.
    -- replace a with 0 in H1; replace b with 0 in H1; try lia. destruct H1 as [x [y H1]]. lia.
    -- pose proof theorem_18_5 a b 1 H2 ltac:(lia) H1 as [H3 _]. pose proof Z.gcd_nonneg a b as H4.
       pose proof (Z.gcd_eq_0_r a b) as H5. pose proof (Z.gcd_eq_0_l a b) as H6.
       assert (Z.gcd a b = 0 \/ Z.gcd a b = 1) as [H7 | H7] by lia; auto. specialize (H5 H7). specialize (H6 H7). lia.
Qed.

Theorem theorem_18_13 : forall a b c,
  (a | b * c) -> Z.gcd a b = 1 -> (a | c).
Proof.
  intros a b c [k H1] H2. apply theorem_18_10 in H2 as [x [y H2]].
  assert (c = 0 \/ c <> 0) as [H3 | H3] by lia.
  - exists 0. lia.
  - exists (c * x + k * y). apply (Z.mul_cancel_l 1 (a * x + b * y) c H3) in H2. rewrite Z.mul_1_r in H2.
    rewrite H2 at 1. replace (c * (a * x + b * y)) with (c * a * x + b * c * y) by lia. rewrite H1. lia.
Qed.

Theorem theorem_18_15 : forall a b c,
  (a | c) -> (b | c) -> Z.gcd a b = 1 -> (a * b | c).
Proof.
  intros a b c [k H1] [l H2] H3. apply theorem_18_10 in H3 as [x [y H3]].
  assert (c = 0 \/ c <> 0) as [H4 | H4] by lia.
  - exists 0. lia.
  - exists (k * y + l * x). apply (Z.mul_cancel_l 1 (a * x + b * y) c H4) in H3. rewrite Z.mul_1_r in H3.
    rewrite H3 at 1. replace ((k * y + l * x) * (a * b)) with (k * a * y * b + l * b * x * a) by lia.
    rewrite <- H1, <- H2. nia.
Qed.

Fixpoint gcd_helper (a b : Z) (n : nat) {struct n} : Z := 
  match n with
  | O => 0
  | S n' => if b =? 0 then a else gcd_helper b (a mod b) n'
  end.

Definition gcd_Z (a b : Z) : Z :=
  let a' := Z.max (Z.abs a) (Z.abs b) in
  let b' := Z.min (Z.abs a) (Z.abs b) in
  gcd_helper a' b' (Z.to_nat b' + 1).

Compute gcd_Z 20 20.
Compute Z.gcd 20 20.
  
Lemma gcd_helper_correct : forall a b n,
  a >= b -> b >= 0 -> (n >= Z.to_nat (b + 1))%nat -> gcd_helper a b n = Z.gcd a b.
Proof.
  intros a b n H1 H2 H3. generalize dependent b. generalize dependent a. induction n as [| k IH].
  - intros a b H1 H2 H3. assert (b = 0) as H4 by lia. rewrite H4. simpl. rewrite Z.gcd_0_r. lia.
  - intros a b H1 H2 H3. simpl. assert (b = 0 \/ b > 0) as [H4 | H4] by lia.
    -- rewrite H4. simpl. rewrite Z.gcd_0_r. lia.
    -- assert (b =? 0 = false) as H5 by lia. rewrite H5. specialize (IH b (a mod b)).
       pose proof Z.mod_pos_bound a b (ltac : (lia)) as H6. pose proof Z_mod_nonneg_nonneg a b (ltac : (lia)) as H7.
       specialize (IH ltac:(lia) ltac:(lia)). rewrite IH; try lia. rewrite Z.gcd_comm. rewrite Z.gcd_mod. apply Z.gcd_comm. lia.
Qed.

Theorem gcd_Z_correct : forall a b,
  gcd_Z a b = Z.gcd a b.
Proof.
  intros a b. unfold gcd_Z. pose proof (Z.lt_trichotomy (Z.abs a) (Z.abs b)) as [H1 | [H1 | H1]].
  - replace (Z.max (Z.abs a) (Z.abs b)) with (Z.abs b) by lia. replace (Z.min (Z.abs a) (Z.abs b)) with (Z.abs a) by lia.
    rewrite <- Z.gcd_abs_r. rewrite <- Z.gcd_abs_l. rewrite Z.gcd_comm. apply gcd_helper_correct; lia.
  - replace (Z.max (Z.abs a) (Z.abs b)) with (Z.abs a) by lia. replace (Z.min (Z.abs a) (Z.abs b)) with (Z.abs b) by lia.
    rewrite <- Z.gcd_abs_r. rewrite <- Z.gcd_abs_l. apply gcd_helper_correct; lia.
  - replace (Z.max (Z.abs a) (Z.abs b)) with (Z.abs a) by lia. replace (Z.min (Z.abs a) (Z.abs b)) with (Z.abs b) by lia.
    rewrite <- Z.gcd_abs_r. rewrite <- Z.gcd_abs_l. apply gcd_helper_correct; lia.
Qed.

Lemma lemma_18_2 : forall a n,
  Z.gcd a n = 1 -> exists b, a * b ≡ 1 (mod n).
Proof.
  intros a n H1. apply theorem_18_10 in H1 as [x [y H1]]. exists x, (-y). lia.
Qed.

Lemma lemma_18_3_a : 
  (forall a b d, b <> 0 -> d = Z.gcd a b -> Z.gcd a (b/d) = 1) -> False.
Proof.
  intros H1. specialize (H1 2 4 2 ltac:(lia) ltac:(compute; lia)). compute in H1. lia.
Qed.

Lemma lemma_18_3_b : forall a b c d,
  c > 0 -> (c | a) -> (c | b) -> linear_combination a b c -> d = Z.gcd a b -> c = d.
Proof.
  intros a b c d H0 H1 H2 H3 H4. pose proof gcd_satisfies_gcd_theory a b as H5. unfold gcd_theory in H5.
  assert (a = 0 /\ b = 0 \/ a <> 0 \/ b <> 0) as [[H6 H7] | H6] by lia.
  - rewrite H6, H7 in H4. compute in H4. destruct H3 as [x [y H3]]. lia.
  - assert ((a =? 0) && (b =? 0) = false) as H7 by lia. rewrite H7 in H5. destruct H5 as [H8 [H9 H10]].
    specialize (H10 c ltac:(auto)). rewrite <- H4 in H10. rewrite <- H4 in H8, H9. destruct H8 as [j H8]. destruct H9 as [k H9].
    destruct H3 as [x1 [y1 H3]]. rewrite H8, H9 in H3. assert (d | c) as H11. { exists (j * x1 + k * y1). lia. }
    apply (Z.divide_pos_le) in H11; lia.
Qed.

Lemma lemma_18_4 : forall a b n d,
  d = Z.gcd a b -> (d | n) <-> linear_combination a b n.
Proof.
  intros a b n d H1. split; intros H2.
  - destruct H2 as [k H2]. pose proof gcd_is_linear_combination a b as [x [y H3]]. rewrite <- H1 in H3.
    exists (k * x), (k * y). lia.
  - pose proof gcd_satisfies_gcd_theory a b as H3. unfold gcd_theory in H3. assert (a = 0 /\ b = 0 \/ a <> 0 \/ b <> 0) as [[H4 H5] | H4] by lia.
    -- rewrite H4, H5 in H1. compute in H1. destruct H2 as [x [y H2]]. exists 0. lia.
    -- assert ((a =? 0) && (b =? 0) = false) as H6 by lia. rewrite H6 in H3. clear H4 H6. destruct H3 as [H3 [H4 _]].
       destruct H2 as [x [y H2]]. destruct H3 as [j H3]. destruct H4 as [k H4]. rewrite <- H1 in H3, H4.
       exists (j * x + k * y). lia.
Qed.

Lemma lemma_18_5 : forall a b c d,
  Z.gcd a b = 1 -> (c | a) -> (d | b) -> Z.gcd c d = 1.
Proof.
  intros a b c d H1 H2 H3. pose proof classic (Z.gcd c d = 1) as [H4 | H4]; auto.
  pose proof Z.gcd_nonneg c d as H5. assert (Z.gcd c d = 0 \/ Z.gcd c d > 1) as [H6 | H6] by lia.
  - apply gcd_0 in H6 as [H6 H7]. rewrite H6 in H2. rewrite H7 in H3. destruct H2 as [j H2]. destruct H3 as [k H3].
    replace a with 0 in H1; replace b with 0 in H1; try lia. compute in H1. lia. 
  - pose proof gcd_satisfies_gcd_theory c d as H7. unfold gcd_theory in H7. assert (c = 0 /\ d = 0 \/ c <> 0 \/ d <> 0) as [[H8 H9] | H8] by lia.
    { rewrite H8, H9 in H6. replace (Z.gcd 0 0) with 0 in H6 by (compute; lia). lia. }
    assert ((c =? 0) && (d =? 0) = false) as H10 by lia. rewrite H10 in H7. clear H8 H10. destruct H7 as [H7 [H8 _]].
    assert (H9 : (Z.gcd c d | a)). { apply Z.divide_trans with (m := c); auto. }
    assert (H10 : (Z.gcd c d | b)). { apply Z.divide_trans with (m := d); auto. }
    pose proof (gcd_satisfies_gcd_theory a b) as H11. unfold gcd_theory in H11. assert (a = 0 /\ b = 0 \/ a <> 0 \/ b <> 0) as [[H12 H13] | H12] by lia.
    { rewrite H12, H13 in H1. compute in H1. lia. }
    assert ((a =? 0) && (b =? 0) = false) as H14 by lia. rewrite H14 in H11. clear H12 H14. destruct H11 as [H11 [H12 H13]].
    specialize (H13 (Z.gcd c d) ltac:(auto)). lia.
Qed.

Lemma lemma_18_6_a : forall a b d,
  (a <> 0 \/ b <> 0) -> d = Z.gcd a b -> Z.gcd (a/d) (b/d) = 1.
Proof.
  intros a b d H1 H2. pose proof gcd_is_linear_combination a b as [x1 [y1 H3]]. rewrite <- H2 in H3.
  pose proof gcd_satisfies_gcd_theory a b as H4. unfold gcd_theory in H4. assert (a = 0 /\ b = 0 \/ a <> 0 \/ b <> 0) as [[H5 H6] | H5] by lia.
  { rewrite H5, H6 in H2. compute in H2. lia. }
  assert ((a =? 0) && (b =? 0) = false) as H7 by lia. rewrite H7 in H4. clear H5 H7. destruct H4 as [H4 [H5 H6]].
  rewrite <- H2 in H4, H5. destruct H4 as [j H4]. destruct H5 as [k H5].
  assert (a / d = j) as H7. { rewrite H4. apply Z.div_mul. lia. } assert (b / d = k) as H9. { rewrite H5. apply Z.div_mul. lia. }
  rewrite theorem_18_10. exists x1, y1. nia.
Qed.

Lemma lemma_18_6_b : forall a b,
  b <> 0 -> exists r s, s <> 0 /\ a / b = r / s /\ Z.gcd r s = 1.
Proof.
  intros a b H1. set (d := Z.gcd a b). pose proof gcd_is_linear_combination a b as [x [y H2]].
  pose proof gcd_satisfies_gcd_theory a b as H3. unfold gcd_theory in H3. assert (a = 0 /\ b = 0 \/ a <> 0 \/ b <> 0) as [[H4 H5] | H4] by lia.
  { rewrite H4, H5 in H3. compute in H3. lia. } assert ((a =? 0) && (b =? 0) = false) as H6 by lia. rewrite H6 in H3. clear H4 H6.
  destruct H3 as [H3 [H4 H5]]. assert (d <> 0) as H6. { intros H6. unfold d in H6. apply gcd_0 in H6; lia. } pose proof Z.gcd_nonneg a b as H7.
  exists (a / d), (b / d). repeat split.
  - intros H8. apply Z.div_small_iff in H8 as [H8 | H8]; try lia. pose proof (Z.divide_pos_le d b ltac:(lia) ltac:(auto)) as H9. lia.
  - fold d in H3, H4. destruct H3 as [j H3]. destruct H4 as [k H4]. rewrite H3, H4. rewrite Zdiv_mult_cancel_r; repeat rewrite Z.div_mul; lia.
  - apply lemma_18_6_a; auto.
Qed.

Lemma lemma_18_6_c : forall a b,
  b <> 0 -> exists r s, s > 0 /\ a / b = r / s /\ Z.gcd r s = 1.
Proof.
  intros a b H1. pose proof lemma_18_6_b a b H1 as [r [s [H2 [H3 H4]]]]. 
  pose proof Z.lt_trichotomy (s) 0 as [H5 | [H5 | H5]]; try lia.
  - exists (-r), (-s). repeat split; try nia. rewrite H3. rewrite Z.div_opp_opp; lia. rewrite Z.gcd_opp_l. rewrite Z.gcd_opp_r. auto.
  - exists r, s. repeat split; try lia.
Qed.

(*we need to be careful to turn our integers into real numbers or will fail*)
Lemma lemma_18_6_d_fail : (forall r r' s s',
  s > 0 -> s' > 0 -> r / s = r' / s' -> Z.gcd r s = 1 -> Z.gcd r' s' = 1 -> s = s' /\ r = r') -> False.
Proof.
  intros H1. specialize (H1 7 3 2 1 ltac:(lia) ltac:(lia) ltac:(compute; lia) ltac:(compute; lia) ltac:(compute; lia)). lia.
Qed.

Lemma lemma_18_6_d : forall r r' s s',
  s > 0 -> s' > 0 -> (IZR r / IZR s = IZR r' / IZR s')%R -> Z.gcd r s = 1 -> Z.gcd r' s' = 1 -> s = s' /\ r = r'.
Proof.
  intros r r' s s' H1 H2 H3 H4 H5. apply Rmult_eq_compat_r with (r := IZR s) in H3. apply Rmult_eq_compat_r with (r := IZR s') in H3.
  field_simplify in H3; try (apply not_0_IZR; lia). repeat rewrite <- mult_IZR in H3. apply eq_IZR in H3. split.
  - assert ((s' | r' * s)) as H6. { exists r. lia. } assert ((s | r * s')) as H7. { exists r'. lia. }
    assert (s' | s) as H8. { rewrite Z.gcd_comm in H5. apply theorem_18_13 with (b := r'); auto. }
    assert (s | s') as H9. { rewrite Z.gcd_comm in H4. apply theorem_18_13 with (b := r); auto. }
    assert (s <= s' /\ s' <= s) as H10. { split; apply (Z.divide_pos_le) in H8; apply (Z.divide_pos_le) in H9; lia. } lia.
  - assert (r' | r * s') as H6. { exists s. lia. } assert (r | r' * s) as H7. { exists s'. lia. }
    assert (r' | r) as H8. { rewrite Z.mul_comm in H6. apply theorem_18_13 with (b := s'); auto. }
    assert (r | r') as H9. { rewrite Z.mul_comm in H7. apply theorem_18_13 with (b := s); auto. }
    assert (r = 0 /\ r' = 0 \/ (r <> 0 /\ r' <> 0)) as [H10 | [H10 H11]] by lia; try lia.
    assert (r < 0 /\ r' < 0 \/ r > 0 /\ r' > 0) as [H12 | H12] by lia; try lia.
    -- assert (-r <= -r' /\ -r' <= -r) as H13. 
       {  
          apply Z.divide_opp_l in H8. apply Z.divide_opp_r in H8. apply Z.divide_opp_l in H9. apply Z.divide_opp_r in H9. split;
          apply (Z.divide_pos_le) in H8; apply (Z.divide_pos_le) in H9; lia. 
       } lia.
    -- apply (Z.divide_pos_le) in H8; apply (Z.divide_pos_le) in H9; lia. 
Qed.

Definition lcm_theory (a b lcm : Z) : Prop :=
  (a | lcm) /\ (b | lcm) /\ (forall m, (a | m) -> (b | m) -> m > 0 -> lcm <= m).

Lemma lcm_satisfies_lcm_theory : forall a b,
  lcm_theory a b (Z.lcm a b).
Proof.
  intros a b. unfold lcm_theory. repeat split; try (apply Z.divide_lcm_l); try (apply Z.divide_lcm_r).
  intros m H1 H2 H3. pose proof Z.lcm_least a b m H1 H2 as H4.
  pose proof (Z.lcm_nonneg a b) as H5. assert (0 = Z.lcm a b \/ 0 < Z.lcm a b) as [H6 | H6] by lia.
  - rewrite <- H6 in H4. apply Z.divide_0_l in H4. lia.
  - apply Z.divide_pos_le in H1; try lia. apply Z.divide_pos_le in H2; try lia. apply Z.divide_pos_le in H4; try lia.
Qed.

Lemma exists_common_multiple : forall a b,
  a > 0 -> b > 0 -> exists m, m > 0 /\ (a | m) /\ (b | m).
Proof.
  intros a b. pose proof Z.divide_lcm_l a b as H1. pose proof Z.divide_lcm_r a b as H2. exists (Z.lcm a b). split; auto.
  pose proof (Z.lcm_nonneg a b) as H3. assert (Z.lcm a b = 0 \/ 0 < Z.lcm a b) as [H4 | H4] by lia; try lia.
  apply Z.lcm_eq_0 in H4. lia.
Qed.

Lemma lemma_18_7 : forall a b,
  a > 0 -> b > 0 -> Z.lcm a b = a * b / Z.gcd a b.
Proof.
  intros a b Ha_pos Hb_pos. pose proof gcd_satisfies_gcd_theory a b as H1. unfold gcd_theory in H1.
  assert (a = 0 /\ b = 0 \/ a <> 0 \/ b <> 0) as [[H2 H3] | H2] by lia.
  { rewrite H2, H3. compute. lia. } assert ((a =? 0) && (b =? 0) = false) as H4 by lia. rewrite H4 in H1. clear H2 H4.
  destruct H1 as [[j H1] [[k H2] H3]]. set (d := Z.gcd a b). assert (d | a * b) as [l H4]. { exists (j * b); lia. }
  assert (H5 : d * l = d * j * b). { nia. } assert (H6 : d * l = d * k * a). { nia. } pose proof (Z.gcd_nonneg a b) as H7.
  assert (H8 : l = k * a). { apply Z.mul_cancel_l with (p := d); lia. } assert (H9 : l = j * b). { apply Z.mul_cancel_l with (p := d); lia. } 
  assert (H10 : (a | l)). { exists k; lia. } assert (H11 : (b | l)). { exists j; lia. }
  pose proof lcm_satisfies_lcm_theory a b as [H12 [H13 H14]]. specialize (H14 l H10 H11 ltac:(lia)).
  pose proof (gcd_is_linear_combination a b) as [x [y H15]]. fold d in H15.
  assert (H16 : forall m, m > 0 -> (a | m) -> (b | m) -> (l | m)).
  {
    intros m H16 [p H17] [q H18]. assert (H19 : m * d = d * l * (q * x + p * y)).
    {
       apply Z.mul_cancel_l with (p := m) in H15; try lia. rewrite Z.mul_add_distr_l in H15. replace (m * (a * x)) with (b * q * a * x) in H15 by lia.
       replace (m * (b * y)) with (a * p * b * y) in H15. 2 : { rewrite H17. lia. } lia. 
    }
    assert (H20 : m = l * (q * x + p * y)). { apply Z.mul_cancel_l with (p := d); lia. }
    assert (H21 : (l | m)). { exists (q * x + p * y). lia. } auto.
  }
  assert (H17 : l = Z.lcm a b).
  {
    specialize (H16 (Z.lcm a b)). pose proof (Z.lcm_nonneg a b) as H17. assert (Z.lcm a b = 0 \/ 0 < Z.lcm a b) as [H18 | H18] by lia; try lia.
    - apply Z.lcm_eq_0 in H18. lia.
    - specialize (H16 ltac:(lia) ltac:(auto) ltac:(auto)). apply Z.divide_pos_le in H16; lia.
  }
  rewrite <- H17. rewrite H4. rewrite Z.div_mul; lia.
Qed.