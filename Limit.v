Require Import Imports Sequence Sets Chapter12 Reals_util Sequence Notations Utf8 Functions.
Import SetNotations.

Open Scope R_scope.

Record Rsub (P : Ensemble ℝ) : Type := mkRsub { val : ℝ; prop : In _ P val }.

Definition limit (f : ℝ -> ℝ) (a L : ℝ) : Prop :=
  ∀ ε, ε > 0 -> ∃ δ, δ > 0 /\ ∀ x, 0 < |x - a| < δ -> |f x - L| < ε.

Definition left_limit (f : ℝ -> ℝ) (a L : ℝ) : Prop :=
  ∀ ε, ε > 0 -> ∃ δ, δ > 0 /\ ∀ x, 0 < a - x < δ -> |f x - L| < ε.

Definition right_limit (f : ℝ -> ℝ) (a L : ℝ) : Prop :=
  ∀ ε, ε > 0 -> ∃ δ, δ > 0 /\ ∀ x, 0 < x - a < δ -> |f x - L| < ε.

Notation "⟦ 'lim' a ⟧ f '=' L" := 
  (limit f a L) 
    (at level 70, f at level 0, no associativity, format "⟦  'lim'  a  ⟧  f  '='  L").

Notation "⟦ 'lim' a ⁺ ⟧ f '=' L" := 
  (right_limit f a L)
    (at level 70, f at level 0, no associativity, format "⟦  'lim'  a ⁺  ⟧  f  '='  L").

Notation "⟦ 'lim' a ⁻ ⟧ f '=' L" :=
  (left_limit f a L)
    (at level 70, f at level 0, no associativity, format "⟦  'lim'  a ⁻  ⟧  f  '='  L").

Lemma left_right_iff : forall f a L,
  ⟦ lim a ⟧ f = L ↔ ⟦ lim a⁻ ⟧ f = L ∧ ⟦ lim a⁺ ⟧ f = L.
Proof.
  intros f a L. split.
  - intros H1. split.
    -- intros ε H2. specialize (H1 ε H2) as [δ [H3 H4]]. exists δ. split; auto. intros x H5. specialize (H4 x). solve_R.
    -- intros ε H2. specialize (H1 ε H2) as [δ [H3 H4]]. exists δ. split; auto. intros x H5. specialize (H4 x). solve_R.
  - intros [H1 H2] ε H3. specialize (H1 ε H3) as [δ1 [H4 H5]]. specialize (H2 ε H3) as [δ2 [H6 H7]]. set (δ := Rmin δ1 δ2).
    assert (δ > 0) as H8 by (unfold δ; solve_min). assert (δ <= δ1 /\ δ <= δ2) as [H9 H10] by (unfold δ; solve_min).
    exists δ. split; auto. intros x H11. specialize (H5 x). specialize (H7 x). solve_R.
Qed.

Lemma lemma_1_20 : forall x x0 y y0 ε,
  |x - x0| < ε / 2 -> |y - y0| < ε / 2 -> |(x + y) - (x0 + y0)| < ε /\ |(x - y) - (x0 - y0)| < ε.
Proof.
  solve_abs.
Qed.

Lemma lemma_1_21 : forall x x0 y y0 ε,
  |x - x0| < Rmin (ε / (2 * (|y0| + 1))) 1 -> |y - y0| < ε / (2 * (|x0| + 1)) -> |x * y - x0 * y0| < ε.
Proof.
  intros x x0 y y0 ε H1 H2. assert (H3 : (Rabs (x - x0)) < 1). { apply Rlt_gt in H1. apply Rmin_Rgt_l in H1. lra. }
  assert (H4 : Rabs x - Rabs x0 < 1). { pose proof Rabs_triang_inv x x0. lra. }
  assert (H5 : Rabs (y - y0) >= 0) by (apply Rle_ge; apply Rabs_pos).
  assert (H6 : Rabs x0 >= 0) by (apply Rle_ge; apply Rabs_pos).
  assert (H7 : ε > 0).
  { 
    pose proof Rtotal_order ε 0 as [H7 | [H7 | H7]].
    - assert (H8 : ε / (2 * (Rabs x0 + 1)) < 0). { apply Rdiv_neg_pos. lra. lra. } lra.
    - nra.
    - apply H7.
  }
  assert (H8 : Rabs x < 1 + Rabs x0) by lra. replace (x * y - x0 * y0) with (x * (y - y0) + y0 * (x - x0)) by lra.
  assert (H9 : Rabs (x * (y - y0) + y0 * (x - x0)) <= Rabs x * Rabs (y - y0) + Rabs y0 * Rabs (x - x0)) by solve_abs.
  assert (H10 : (1 + Rabs x0) * (ε / (2 * (Rabs x0 + 1))) = ε / 2). { field; try unfold Rabs; try destruct Rcase_abs; try nra. }
  assert (H11 : forall x, x >= 0 -> x / (2 * (x + 1)) < 1 / 2).
  {
    intros x1 H11. apply Rmult_lt_reg_l with (r := 2). lra. unfold Rdiv.
    replace (2 * (1 * / 2)) with (1) by lra. replace (2 * (x1 * / (2 * (x1 + 1)))) with ((x1) * (2 * / (2 * (x1 + 1)))) by lra.
    rewrite Rinv_mult. replace (2 * (/ 2 * / (x1 + 1))) with (2 * / 2 * / (x1 + 1)) by nra. rewrite Rinv_r. 2 : lra.
    rewrite Rmult_1_l. rewrite <- Rdiv_def. apply Rdiv_lt_1. lra. lra.
  }
  assert (H12 : (Rabs y0 * (ε / (2 * ((Rabs y0) + 1)))) < ε / 2). 
  { 
    replace (Rabs y0 * (ε / (2 * (Rabs y0 + 1)))) with (ε * (Rabs y0 * / (2 * (Rabs y0 + 1)))) by lra.
    pose proof H11 (Rabs y0) as H12. unfold Rdiv. apply Rmult_lt_compat_l. lra. unfold Rdiv in H12. rewrite Rmult_1_l in H12.
    apply H12. apply Rle_ge. apply Rabs_pos.
  }
  replace (ε) with (ε / 2 + ε / 2) by lra. 
  assert (H13 : Rabs x * Rabs (y - y0) < ((1 + Rabs x0) * (ε / (2 * (Rabs x0 + 1))))) by nra.
  assert (H14 : Rabs (x - x0) < (ε / (2 * (Rabs y0 + 1)))). { apply Rlt_gt in H1. apply Rmin_Rgt_l in H1. lra. }
  assert (H15 : Rabs y0 >= 0) by (apply Rle_ge; apply Rabs_pos).
  assert (H16 : Rabs (x - x0) >= 0) by (apply Rle_ge; apply Rabs_pos).
  assert (H17 : Rabs y0 * Rabs (x - x0) <= (Rabs y0 * (ε / (2 * ((Rabs y0 + 1)))))) by nra.
  nra.
Qed.

Lemma lemma_1_22 : forall y y0 ε,
  y0 <> 0 -> |y - y0| < Rmin (|y0| / 2) ((ε * |y0|^2) / 2) -> y <> 0 /\ |1 / y - 1 / y0| < ε.
Proof.
  intros y y0 eps H1 H2. assert (H3 : y <> 0).
  - assert (H4 : Rabs (y - y0) < Rabs (y0 / 2)). { apply Rlt_gt in H2. apply Rmin_Rgt_l in H2. solve_abs. } solve_abs.
  - split.
    -- apply H3.
    -- assert (H4 : Rabs (y - y0) < Rabs (y0 / 2)). { apply Rlt_gt in H2. apply Rmin_Rgt_l in H2. solve_abs. }
       assert (H5 : Rabs (y - y0) < (eps * (Rabs y0)^2) / 2). { apply Rlt_gt in H2. apply Rmin_Rgt_l in H2. lra. }
       assert (H6 : Rabs y > Rabs y0 / 2) by solve_abs.
       assert (H7 : Rabs y > 0) by solve_abs. assert (H8 : Rabs y0 > 0) by solve_abs.
       assert (H9 : forall a b : R, a > 0 -> b > 0 -> a > b / 2 -> 1 / a < 2 / b).
       { 
          intros a b H9 H10 H11. apply Rmult_lt_reg_r with (r := a). lra. replace (1 / a * a) with 1 by (field; lra).
          apply Rmult_lt_reg_r with (r := b). lra. replace (2 / b * a * b) with (2 * a) by (field; lra). lra.
       }
       assert (H10 : 1 / Rabs y < 2 / Rabs y0). { apply H9. apply H7. apply H8. apply H6. } clear H9.
       replace (1 / y - 1 / y0) with ((y0 - y) / (y * y0)) by (field; lra). 
       unfold Rdiv. rewrite Rabs_mult. rewrite Rabs_inv. rewrite <- Rdiv_def. rewrite Rabs_mult.
       rewrite Rabs_minus_sym. assert (H11 : 2 * Rabs (y - y0) < eps * Rabs y0 ^ 2). { lra. }
       assert (H12 : (2 * Rabs (y - y0)) / (Rabs y0 ^ 2) < eps).
       { apply Rmult_lt_reg_r with (r := Rabs y0 ^ 2). nra. apply Rmult_lt_reg_r with (r := / 2). nra.
          replace (2 * Rabs (y - y0) / (Rabs y0 ^ 2) * Rabs y0 ^2 * / 2) with 
          (2 * Rabs (y - y0) * / 2) by (field; lra). lra.
       }
       replace (2 * Rabs (y - y0) / Rabs y0 ^ 2) with (Rabs (y - y0) / ((Rabs y0 / 2) * Rabs y0)) in H12 by (field; nra).
       assert (H13 : (Rabs y0 / 2 * Rabs y0) < Rabs y * Rabs y0) by nra. 
       assert (H14 : forall a b c, a > 0 -> b > 0 -> c >= 0 -> a > b -> c / a <= c / b).
       {
          intros a b c H14 H15 H16 H17. apply Rmult_le_reg_r with (r := a). lra.
          replace (c / a * a) with c by (field; lra). apply Rmult_le_reg_r with (r := b). lra.
          replace (c / b * a * b) with (c * a) by (field; lra). nra.
       }
       assert (H15 : Rabs (y - y0) / (Rabs y0 / 2 * Rabs y0) >= Rabs (y - y0) / (Rabs y * Rabs y0)). 
       { apply Rle_ge. apply H14. nra. nra. apply Rle_ge. apply Rabs_pos. nra. }
       nra.
Qed. 

Notation "f + g" := (fun x : ℝ => f x + g x) (at level 50, left associativity) : function_scope.
Notation "f - g" := (fun x : ℝ => f x - g x) (at level 50, left associativity) : function_scope.
Notation "f ∙ g" := (fun x : ℝ => f x * g x) (at level 40, left associativity) : function_scope.
Notation "f ∕ g" := (fun x : ℝ => f x / g x) (at level 40, left associativity) : function_scope.
Notation "f ∘ g" := (fun x : ℝ => f (g x)) (at level 40, left associativity) : function_scope.
Notation "c * f" := (fun x : ℝ => c * f x) (at level 40, left associativity) : function_scope.
Notation "f ^ n" := (fun x : ℝ => (f x) ^ n) (at level 30, right associativity) : function_scope.

Lemma limit_of_function_unique : forall f a L1 L2,
  ⟦ lim a ⟧ f = L1 -> ⟦ lim a ⟧ f = L2 -> L1 = L2. 
Proof.
  intros f a L1 L2 H1 H2. pose proof (classic (L1 = L2)) as [H3 | H3]; auto.
  specialize (H1 (|L1 - L2| / 2) ltac:(solve_abs)) as [δ1 [H4 H5]].
  specialize (H2 (|L1 - L2| / 2) ltac:(solve_abs)) as [δ2 [H6 H7]].
  set (δ := Rmin δ1 δ2). set (x := a + δ / 2). assert (δ <= δ1 /\ δ <= δ2) as [H8 H9] by (unfold δ; solve_min).
  assert (0 < δ / 2) as H10 by (apply Rdiv_pos_pos; solve_R). assert (x > a) as H11 by (unfold x; solve_min).
  assert (0 < |x - a| < δ) as H12 by (unfold x; solve_R). specialize (H5 x ltac:(solve_R)). specialize (H7 x ltac:(solve_R)).
  assert (|L1 - L2| < |L1 - L2|) as H13.
  {
    assert (|(L1 - f x + (f x - L2))| <= |L1 - f x| + |f x - L2|) as H22 by (apply Rabs_triang).
    rewrite Rabs_minus_sym in H22. 
    assert (|f x - L1| + |f x - L2| < |L1 - L2| / 2 + |L1 - L2| / 2) as H23 by lra.
    field_simplify in H23. rewrite Rmult_div_r in H23; auto.
    replace (L1 - f x + (f x - L2)) with (L1 - L2) in H22 by lra. lra.
  } lra.
Qed.

Lemma limit_plus : forall f1 f2 a L1 L2,
  ⟦ lim a ⟧ f1 = L1 -> ⟦ lim a ⟧ f2 = L2 -> ⟦ lim a ⟧ (f1 + f2) = (L1 + L2).
Proof.
  intros f1 f2 a L1 L2 H1 H2 ε H3. specialize (H1 (ε / 2) ltac:(lra)) as [δ1 [H4 H5]].
  specialize (H2 (ε / 2) ltac:(lra)) as [δ2 [H6 H7]]. set (δ := Rmin δ1 δ2).
  assert (δ > 0) as H8 by (unfold δ; solve_min). exists δ. split. lra.
  intros x H9. assert (0 < |x - a| < δ1 /\ 0 < |x - a| < δ2) as [H10 H11] by (unfold δ in H9; solve_min).
  specialize (H5 x H10). specialize (H7 x H11). apply lemma_1_20; auto.
Qed.

Lemma limit_const : forall a c,
  ⟦ lim a ⟧ (fun _ => c) = c.
Proof.
  intros a c ε H1. exists 1; split; solve_abs.
Qed.

Lemma limit_id : forall a,
  ⟦ lim a ⟧ (fun x => x) = a.
Proof.
  intros a ε H1. exists ε. split; solve_abs.
Qed.

Lemma limit_minus : forall f1 f2 a L1 L2,
  ⟦ lim a ⟧ f1 = L1 -> ⟦ lim a ⟧ f2 = L2 -> ⟦ lim a ⟧ (f1 - f2) = (L1 - L2).
Proof.
   intros f1 f2 a L1 L2 H1 H2. unfold Rminus. apply limit_plus; auto.
   intros ε H3. specialize (H2 ε H3) as [δ [H4 H5]].
   exists δ. split; auto. intros x H6. apply H5 in H6. solve_abs.
Qed.

Lemma limit_mult : forall f1 f2 a L1 L2,
  ⟦ lim a ⟧ f1 = L1 -> ⟦ lim a ⟧ f2 = L2 -> ⟦ lim a ⟧ (f1 ∙ f2) = L1 * L2.
Proof.
  intros f1 f2 a L1 L2 H1 H2 ε H3. assert (ε / (2 * ((|L2|) + 1)) > 0 /\ ε / (2 * ((|L1|) + 1)) > 0) as [H4 H5].
  { split; apply Rdiv_pos_pos; solve_abs. }
  specialize (H1 (Rmin (ε / (2 * ((|L2|) + 1))) 1) ltac:(solve_min)) as [δ1 [H6 H7]].
  specialize (H2 (ε / (2 * ((|L1|) + 1))) ltac:(solve_min)) as [δ2 [H8 H9]].
  set (δ := Rmin δ1 δ2). assert (δ > 0) as H10 by (unfold δ; solve_min). exists δ. split. lra.
  intros x H11. assert (0 < |x - a| < δ1 /\ 0 < |x - a| < δ2) as [H12 H13] by (unfold δ in H11; solve_min).
  specialize (H7 x H12). specialize (H9 x H13). apply lemma_1_21; auto.
Qed.

Lemma limit_inv : forall f a L,
  ⟦ lim a ⟧ f = L -> L <> 0 -> ⟦ lim a ⟧ (fun x => 1 / f x) = / L.
Proof.
  intros f a L H1 H2 ε H3. assert (|L| / 2 > 0) as H4 by solve_abs. assert (ε * |L|^2 / 2 > 0) as H5.
  { apply Rmult_lt_0_compat. apply pow2_gt_0 in H2. solve_abs. apply Rinv_pos; lra. }
  specialize (H1 (Rmin (|L| / 2) (ε * |L|^2 / 2)) ltac:(solve_min)) as [δ [H6 H7]].
  exists δ. split. lra. intros x H8. specialize (H7 x H8). repeat rewrite <- Rdiv_1_l.
  apply lemma_1_22; auto.
Qed.

Lemma limit_div : forall f1 f2 a L1 L2,
  ⟦ lim a ⟧ f1 = L1 -> ⟦ lim a ⟧ f2 = L2 -> L2 <> 0 -> ⟦ lim a ⟧ (f1 ∕ f2) = L1 / L2.
Proof.
  intros f1 f2 a L1 L2 H1 H2 H3. replace (f1 ∕ f2)%function with (f1 ∙ (fun x => 1 / f2 x)).
  2 : { extensionality x. lra. }
  unfold Rdiv. apply limit_mult; auto. apply limit_inv; auto.
Qed.

Lemma limit_pow : forall f a L n,
  ⟦ lim a ⟧ f = L -> ⟦ lim a ⟧ (f ^ n) = L ^ n.
Proof.
  intros f a L n H1. induction n as [| n IH].
  - rewrite pow_O. replace ((fun x => f x ^ 0)) with (fun _ : ℝ => 1).
    2 : { extensionality x. rewrite pow_O. reflexivity. } apply limit_const; auto.
  - simpl. apply limit_mult; auto.
Qed.

Lemma sqrt_limit_helper_1 : forall x a,
  x >= 0 -> a >= 0 -> |√x - √a| = |x - a| / (√x + √a).  
Proof.
  intros x a H1 H2. pose proof Rtotal_order x a as [H3 | [H3 | H3]].
  - pose proof sqrt_lt_1_alt x a ltac:(lra) as H4. replace (|(√x - √a)|) with (√a - √x) by solve_abs.
    replace (|x - a|) with (a - x) by solve_abs. pose proof sqrt_lt_R0 a ltac:(lra) as H5. 
    pose proof sqrt_positivity x ltac:(lra) as H6. apply Rmult_eq_reg_r with (r := √x + √a); try nra.
    field_simplify; try nra. repeat rewrite pow2_sqrt; lra.
  - subst. solve_abs.
  - pose proof sqrt_lt_1_alt a x ltac:(lra) as H4. replace (|(√x - √a)|) with (√x - √a) by solve_abs.
    replace (|x - a|) with (x - a) by solve_abs. pose proof sqrt_lt_R0 x ltac:(lra) as H5. 
    pose proof sqrt_positivity a ltac:(lra) as H6. apply Rmult_eq_reg_r with (r := √x + √a); try nra.
    field_simplify; try nra. repeat rewrite pow2_sqrt; lra.
Qed.

Lemma sqrt_limit_helper_2 : forall x a,
  a >= 0 -> |x - a| < a / 2 -> √x + √a > √(a/2) + √a.
Proof.
  intros x a H1 H2. pose proof Rtotal_order x a as [H3 | [H3 | H3]].
  - replace (|x - a|) with (a - x) in H2 by solve_abs. assert (a / 2 < x) as H4 by lra.
    pose proof sqrt_lt_1_alt (a/2) x ltac:(lra) as H5. lra.
  - subst. pose proof sqrt_lt_1_alt (a/2) a ltac:(solve_R) as H5. lra.
  - pose proof sqrt_lt_1_alt (a/2) x ltac:(lra) as H4. lra.
Qed.

Lemma limit_sqrt_x : forall a,
  ⟦ lim a ⟧ (fun x => √x) = √a.
Proof.
  intros a ε H1. assert (a <= 0 \/ a > 0) as [H2 | H2] by lra.
  - exists (ε^2). split. nra. intros x H3. assert (x < a \/ x > a) as [H4 | H4] by solve_abs.
    -- repeat rewrite sqrt_neg_0; solve_abs.
    -- rewrite (sqrt_neg_0 a); try lra. replace (|x - a|) with (x - a) in H3 by solve_abs.
       assert (x < ε ^ 2) as H5 by nra. pose proof sqrt_pos x as H6. replace (|(√x - 0)|) with (√x) by solve_abs.
       apply Rlt_pow_base with (n := 2%nat); try lra; try lia. assert (x <= 0 \/ x > 0) as [H7 | H7] by lra.
       apply sqrt_neg_0 in H7. rewrite H7. lra. rewrite pow2_sqrt; lra.
  - set (δ := Rmin (a / 2) ((√(a/2) + √a) * ε)). exists δ. split.
    -- unfold δ. pose proof sqrt_lt_R0 a ltac:(lra) as H3.
       pose proof sqrt_lt_R0 (a / 2) ltac:(apply Rdiv_pos_pos; lra) as H4. solve_min.
    -- intros x H3. assert (|(x - a)| < a / 2) as H4 by (unfold δ in *; solve_R).
       assert (|(x - a)| < (√(a / 2) + √a) * ε) as H5 by (unfold δ in *; solve_R).
       assert (x < 0 \/ x >= 0) as [H6 | H6] by lra.
       * rewrite sqrt_neg_0; try lra. solve_abs.
       * pose proof sqrt_limit_helper_2 x a ltac:(lra) ltac:(lra) as H7.
         rewrite sqrt_limit_helper_1; try lra. apply Rmult_lt_reg_r with (r := √x + √a); try nra.
         field_simplify; nra.
Qed.

Lemma limit_sqrt : forall f a L,
  ⟦ lim a ⟧ f = L -> L >= 0 -> ⟦ lim a ⟧ (fun x => √(f x)) = √L.
Proof.
Admitted.

Lemma limit_to_0_equiv : forall f1 f2 L,
  (forall x, x <> 0 -> f1 x = f2 x) -> ⟦ lim 0 ⟧ f1 = L -> ⟦ lim 0 ⟧ f2 = L.
Proof.
  intros f1 f2 L H1 H2 ε H3. specialize (H2 ε H3) as [δ [H4 H5]]. exists δ. split; auto.
  intros x H6. specialize (H5 x H6). rewrite <- H1; solve_R.
Qed.

Lemma lim_equality_substitution : forall f a L1 L2,
  L1 = L2 -> ⟦ lim a ⟧ f = L1 -> ⟦ lim a ⟧ f = L2.
Proof.
  intros f a L1 L2 H1 H2 ε H4. specialize (H2 ε H4) as [δ [H5 H6]].
  exists δ; split; auto. intros x. specialize (H6 x). solve_abs.
Qed.

Ltac solve_lim :=
  try solve_R;
  match goal with
  | [ |- ⟦ lim ?a ⟧ ?f = ?rhs ] =>
      let L2' := eval cbv beta in (f a) in
      let L2 := eval simpl in L2' in
      let H := fresh "H" in
      assert (⟦ lim a ⟧ f = L2) as H by
        (repeat (first [
           apply limit_div
         | apply limit_pow
         | apply limit_mult
         | apply limit_inv
         | apply limit_plus
         | apply limit_minus
         | apply limit_sqrt_x
         | apply limit_id
         | apply limit_const
         | solve_R
         ])); apply (lim_equality_substitution f a L2 rhs);
      solve_R; auto
  end.

Lemma f_subtype_independent (P : Ensemble R) (f : Rsub P -> R) (x : R) (H1 H2 : In _ P x) :
  f {| val := x; prop := H1 |} = f {| val := x; prop := H2 |}.
Proof.
  assert ({| val := x; prop := H1 |} = {| val := x; prop := H2 |}) as H3 by (f_equal; apply proof_irrelevance).
  rewrite H3. reflexivity.
Qed.