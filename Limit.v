Require Import Imports Sequence Sets Chapter12 Reals_util Sequence Notations Utf8 Functions.
Import SetNotations.

Open Scope R_scope.

Definition encloses (D : Ensemble ℝ) (a : R) : Prop :=
  exists b c, b < a < c /\ (fun x => b <= x <= c) ⊆ D.

Record Rsub (D : Ensemble ℝ) := mkRsub {
  val :> R;
  prop : val ∈ D
}.

Definition limit (D : Ensemble ℝ) (f : Rsub D -> ℝ) (a L : ℝ) : Prop :=
  encloses D a /\
    (∀ ε, ε > 0 ⇒ ∃ δ, δ > 0 /\ ∀ x : Rsub D, 0 < |x - a| < δ ⇒ |f x - L| < ε).

Definition limit' (f : ℝ -> ℝ) (a L : ℝ) : Prop :=
  ∀ ε, ε > 0 ⇒ ∃ δ, δ > 0 /\ ∀ x, 0 < |x - a| < δ ⇒ |f x - L| < ε.

Notation "⟦ 'lim' a ⟧ f '=' L" := 
  (limit' f a L) 
    (at level 70, f at level 0, no associativity, format "⟦  'lim'  a  ⟧  f  '='  L").

Notation "⟦ 'lim' a ⟧ f D '=' L" := 
  (limit D f a L) 
    (at level 70, f at level 0, D at level 0, no associativity, format "⟦  'lim'  a  ⟧  f  D  '='  L").

Lemma Full_set_encloses : forall a, encloses (Full_set ℝ) a.
Proof.
  intros a. exists (a - 1), (a + 1). split. lra. intros x _. apply Full_intro.
Qed.

Lemma limit_iff_limit' : forall f a L,
  ⟦ lim a ⟧ f = L ⟺ ⟦ lim a ⟧ f (Full_set ℝ) = L.
Proof.
  intros f a L. split; intros H1.
  - split. apply Full_set_encloses. intros ε H2. specialize (H1 ε H2) as [δ [H3 H4]]. exists δ. split; auto.
  - destruct H1 as [H1 H2]. intros ε H3. specialize (H2 ε H3) as [δ [H4 H5]]. exists δ. split; auto.
    intros x. specialize (H5 (mkRsub (Full_set ℝ) x ltac:( apply Full_intro))). simpl in H5. apply H5.
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

Definition f_plus (D : Ensemble R) f1 f2 (x:Rsub D) : R := f1 x + f2 x.
Definition f_opp (D : Ensemble R) f (x:Rsub D) : R := - f x.
Definition f_mult (D : Ensemble R) f1 f2 (x:Rsub D) : R := f1 x * f2 x.
Definition f_mult_c (D : Ensemble R) (a:R) f (x:Rsub D) : R := a * f x.
Definition f_minus (D : Ensemble R) f1 f2 (x:Rsub D) : R := f1 x - f2 x.
Definition f_div (D : Ensemble R) f1 f2 (x:Rsub D) : R := f1 x / f2 x.
Definition f_div_c (D : Ensemble R) (a:R) f (x:Rsub D) : R := a / f x.
Definition f_pow (D : Ensemble R) f n (x:Rsub D) : R := f x ^ n.
Definition f_comp (D1 D2 : Ensemble R) (f1 : (Rsub D2) -> R) (f2 : (Rsub D1) -> (Rsub D2))  (x:Rsub D1) : R := f1 (f2 x).
Definition f_inv (D : Ensemble R) f (x:Rsub D) : R := / f x.
Definition f_mirr (D : Ensemble R) f (x:Rsub D) : R := f (- x).
Definition f_sqrt (D : Ensemble R) (f : Rsub D -> R) (x:Rsub D) : R := sqrt (f x).

Declare Scope f_scope.
Delimit Scope f_scope with f.

Arguments f_plus {D} f1%_f f2%_f x%_R.
Arguments f_opp {D} f%_f x%_R.
Arguments f_mult {D} f1%_f f2%_f x%_R.
Arguments f_mult_c {D} a%_R f%_f x%_R.
Arguments f_minus {D} f1%_f f2%_f x%_R.
Arguments f_div {D} f1%_f f2%_f x%_R.
Arguments f_div_c {D} a%_R f%_f x%_R.
Arguments f_comp {D1 D2} f1%_f f2%_f x%_R.
Arguments f_inv {D} f%_f x%_R.
Arguments f_mirr {D} f%_f x%_R.
Arguments f_pow {D} f%_f n%_nat x%_R.
Arguments f_sqrt {D} f%_f x%_R.

Infix "+" := f_plus : f_scope.
Notation "- x" := (f_opp x) : f_scope.
Infix "∙" := f_mult (at level 40) : f_scope.
Infix "-" := f_minus : f_scope.
Infix "/" := f_div : f_scope.
Infix "^" := f_pow (at level 30) : f_scope.
Infix "*" := f_mult_c : f_scope.
Notation "/ x" := (f_inv x) : f_scope.
Notation "√ f" := (f_sqrt f) (at level 20) : f_scope.
Notation "f1 'o' f2" := (f_comp f1 f2)
  (at level 20, right associativity) : f_scope.

Lemma limit_of_function_unique : forall D f a L1 L2,
  ⟦ lim a ⟧ f D = L1 -> ⟦ lim a ⟧ f D = L2 -> L1 = L2. 
Proof.
  intros D f a L1 L2 [[b [c [H1 H2]]] H3] [_ H4]. pose proof (classic (L1 = L2)) as [H5 | H5]; auto.
  specialize (H3 (|L1 - L2| / 2) ltac:(solve_abs)) as [δ1 [H6 H7]].
  specialize (H4 (|L1 - L2| / 2) ltac:(solve_abs)) as [δ2 [H8 H9]].
  set (δ := Rmin δ1 δ2). set (y := Rmin (a + δ / 2) c).
  assert (δ > 0) as H10 by (unfold δ; solve_min).
  assert (y ∈ D) as H11. { apply H2. unfold In. unfold y. solve_min. }
  set (x := mkRsub D y H11). assert (δ <= δ1 /\ δ <= δ2) as [H12 H13] by (unfold δ; solve_min).
  assert (y <= c /\ y <= a + δ / 2) as [H14 H15] by (unfold y; solve_min).
  assert (y > a) as H16 by (unfold y; solve_min). assert (0 < |y - a| < δ) as H19 by solve_abs.
  assert (0 < |x - a| < δ1 /\ 0 < |x - a| < δ2) as [H20 H21] by (unfold x, δ; simpl; solve_abs).
  specialize (H9 x ltac:(auto)). specialize (H7 x ltac:(auto)).
  (* instead of all this we could just do solve_abs *)
  assert (|L1 - L2| < |L1 - L2|).
  {
    assert (|(L1 - f x + (f x - L2))| <= |L1 - f x| + |f x - L2|) as H22 by (apply Rabs_triang).
    rewrite Rabs_minus_sym in H22. 
    assert (|f x - L1| + |f x - L2| < |L1 - L2| / 2 + |L1 - L2| / 2) as H23 by lra.
    field_simplify in H23. rewrite Rmult_div_r in H23; auto.
    replace (L1 - f x + (f x - L2)) with (L1 - L2) in H22 by lra. lra.
  } lra.
Qed.

Lemma limit_plus : forall D f1 f2 a L1 L2,
  encloses D a -> ⟦ lim a ⟧ f1 D = L1 -> ⟦ lim a ⟧ f2 D = L2 -> ⟦ lim a ⟧ ((f1 + f2)%f) D = (L1 + L2).
Proof.
  intros D f1 f2 a L1 L2 H1 [_ H2] [_ H3]. split; auto.
  intros ε H4. specialize (H2 (ε / 2) ltac:(lra)) as [δ1 [H5 H6]].
  specialize (H3 (ε / 2) ltac:(lra)) as [δ2 [H7 H8]]. set (δ := Rmin δ1 δ2).
  assert (δ > 0) as H9 by (unfold δ; solve_min). exists δ. split. lra.
  intros x H10. assert (0 < |x - a| < δ1 /\ 0 < |x - a| < δ2) as [H11 H12] by (unfold δ in H10; solve_min).
  specialize (H6 x H11). specialize (H8 x H12). apply lemma_1_20; auto.
Qed.

Lemma limit_const : forall D a c,
  encloses D a -> ⟦ lim a ⟧ (fun _ => c) D = c.
Proof.
  intros D a c H1. split; auto. intros ε H2. exists 1. split; solve_abs.
Qed.

Lemma limit_id : forall D a,
  encloses D a -> ⟦ lim a ⟧ (fun x => x) D = a.
Proof.
  intros D a H1. split; auto. intros ε H2. exists ε. split; solve_abs.
Qed.

Lemma f_minus_plus : forall D (f1 f2 : Rsub D -> R),
  (f1 - f2 = f1 + (- f2)%f)%f.
Proof.
  intros D f1 f2. apply functional_extensionality. intros x. unfold f_minus, f_plus, f_opp. lra.
Qed.

Lemma limit_minus : forall D f1 f2 a L1 L2,
  encloses D a -> ⟦ lim a ⟧ f1 D = L1 -> ⟦ lim a ⟧ f2 D = L2 -> ⟦ lim a ⟧ ((f1 - f2)%f) D = L1 - L2.
Proof.
   intros D f1 f2 a L1 L2 H1 H2 [_ H3]. rewrite f_minus_plus. unfold Rminus. apply limit_plus; auto.
   split; auto. intros ε H4. specialize (H3 ε H4) as [δ [H5 H6]].
   exists δ. split; auto. intros x H7. apply H6 in H7. unfold f_opp. solve_abs.
Qed.

Lemma limit_mult : forall D f1 f2 a L1 L2,
  encloses D a -> ⟦ lim a ⟧ f1 D = L1 -> ⟦ lim a ⟧ f2 D = L2 -> ⟦ lim a ⟧ ((f1 ∙ f2)%f) D = L1 * L2.
Proof.
  intros D f1 f2 a L1 L2 H1 [_ H2] [_ H3]. split; auto.
  intros ε H4. assert (ε / (2 * ((|L2|) + 1)) > 0 /\ ε / (2 * ((|L1|) + 1)) > 0) as [H5 H6].
  { split; apply Rdiv_pos_pos; solve_abs. }
  specialize (H2 (Rmin (ε / (2 * ((|L2|) + 1))) 1) ltac:(solve_min)) as [δ1 [H7 H8]].
  specialize (H3 (ε / (2 * ((|L1|) + 1))) ltac:(solve_min)) as [δ2 [H9 H10]].
  set (δ := Rmin δ1 δ2). assert (δ > 0) as H11 by (unfold δ; solve_min). exists δ. split. lra.
  intros x H12. assert (0 < |x - a| < δ1 /\ 0 < |x - a| < δ2) as [H13 H14] by (unfold δ in H12; solve_min).
  specialize (H8 x H13). specialize (H10 x H14). apply lemma_1_21; auto.
Qed.

Lemma limit_inv : forall D f a L,
  encloses D a -> ⟦ lim a ⟧ f D = L -> L <> 0 -> ⟦ lim a ⟧ ((/ f)%f) D = / L.
Proof.
  intros D f a L H1 [_ H2] H3. split; auto.
  intros ε H4. assert (|L| / 2 > 0) as H5 by solve_abs. assert (ε * |L|^2 / 2 > 0) as H6.
  { apply Rmult_lt_0_compat. apply pow2_gt_0 in H3. solve_abs. apply Rinv_pos; lra. }
  specialize (H2 (Rmin (|L| / 2) (ε * |L|^2 / 2)) ltac:(solve_min)) as [δ [H7 H8]].
  exists δ. split. lra. intros x H9. specialize (H8 x H9). repeat rewrite <- Rdiv_1_l. unfold f_inv.
  rewrite <- Rdiv_1_l. apply lemma_1_22; auto.
Qed.

Lemma limit_div : forall D f1 f2 a L1 L2,
  encloses D a -> ⟦ lim a ⟧ f1 D = L1 -> ⟦ lim a ⟧ f2 D = L2 -> L2 <> 0 -> ⟦ lim a ⟧ ((f1 / f2)%f) D = L1 / L2.
Proof.
  intros D f1 f2 a L1 L2 H1 H2 H3 H4. replace (f1 / f2)%f with (f1 ∙ (f_inv f2))%f by reflexivity.
  unfold Rdiv. apply limit_mult; auto. apply limit_inv; auto.
Qed.

Lemma limit_pow : forall D f a L n,
  encloses D a -> ⟦ lim a ⟧ f D = L ⇒ ⟦ lim a ⟧ ((f ^ n)%f) D = L ^ n.
Proof.
  intros D f a L n H1 H2. induction n as [| n IH].
  - rewrite pow_O. replace ((fun x0 => f x0 ^ 0)) with (fun x0 : Rsub D => 1).
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
  ⟦ lim a ⟧ (fun x => √x) (Full_set R) = √a.
Proof.
  intros a. split; try apply Full_set_encloses. intros ε H1. assert (a <= 0 \/ a > 0) as [H2 | H2] by lra.
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

Lemma limit_sqrt : forall D f a L,
  encloses D a -> ⟦ lim a ⟧ f D = L -> L >= 0 -> ⟦ lim a ⟧ ((√f)%f) D = √L.
Proof.
  
Admitted.

Lemma limit_to_0_equiv : forall f1 f2 L,
  (forall x, x <> 0 -> f1 x = f2 x) -> ⟦ lim 0 ⟧ f1 = L -> ⟦ lim 0 ⟧ f2 = L.
Proof.
  intros f1 f2 L H1 H2 ε H3. specialize (H2 ε H3) as [δ [H4 H5]]. exists δ. split; auto.
  intros x H6. specialize (H5 x H6). rewrite <- H1; solve_R.
Qed.

Lemma lim_equality_substitution : forall D f a L1 L2,
  encloses D a -> L1 = L2 -> ⟦ lim a ⟧ f D = L1 -> ⟦ lim a ⟧ f D = L2.
Proof.
  intros D f a L1 L2 H1 H2 [_ H3]. split; auto.
  intros ε H4. specialize (H3 ε H4) as [δ [H5 H6]].
  exists δ; split; auto. intros x. specialize (H6 x). solve_abs.
Qed.

Ltac solve_lim :=
  try solve_R;
  match goal with
  | [ |- ⟦ lim ?a ⟧ ?f = ?rhs ] => apply limit_iff_limit'; solve_lim
  | [ |- ⟦ lim ?a ⟧ ?f (Full_set R) = ?rhs ] =>
      let b := 
        match type of a with
        | R => constr:(mkRsub (Full_set R) a ltac:(apply Full_intro))
        | _ => constr:(a)
        end in
      let L2' := eval cbv beta in (f b) in
      let L2 := eval simpl in L2' in
      let H := fresh "H" in
      assert (⟦ lim a ⟧ f (Full_set R) = L2) as H by
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
         ]);
         try apply Full_set_encloses);
      apply (lim_equality_substitution (Full_set R) f a L2 rhs);
      solve_R; apply Full_set_encloses
  end.

Lemma f_subtype_independent (P : Ensemble R) (f : Rsub P ⇒ R) (x : R) (H1 H2 : In _ P x) :
  f {| val := x; prop := H1 |} = f {| val := x; prop := H2 |}.
Proof.
  assert ({| val := x; prop := H1 |} = {| val := x; prop := H2 |}) as H3 by (f_equal; apply proof_irrelevance).
  rewrite H3. reflexivity.
Qed.

Section limit_with_two_domains.

  Definition f_plus' (D1 D2 : Ensemble ℝ)
                  (f1 : Rsub D1 ⇒ ℝ)
                  (f2 : Rsub D2 ⇒ ℝ)
                  (x : Rsub (D1 ⋂ D2)) : ℝ := 
  let val_x := val (D1 ⋂ D2) x in
  let prop_x_in_intersection := prop (D1 ⋂ D2) x in
  let prop_x_D1_D2 := proj1 (In_Intersection_def ℝ D1 D2 x) prop_x_in_intersection in
  let prop_x_D1 := proj1 prop_x_D1_D2 in
  let prop_x_D2 := proj2 prop_x_D1_D2 in
  f1 (mkRsub D1 val_x prop_x_D1) + f2 (mkRsub D2 val_x prop_x_D2).
  
  Variable D1 D2 : Ensemble ℝ.
  Variable f1 : Rsub D1 ⇒ ℝ.
  Variable f2 : Rsub D2 ⇒ ℝ.
  Let f3 : Rsub (D1 ⋂ D2) ⇒ ℝ := f_plus' D1 D2 f1 f2. 
  Variable a L1 L2 : ℝ.

  Lemma limit_plus'' : encloses (D1 ⋂ D2) a -> ⟦ lim a ⟧ f1 D1 = L1 -> ⟦ lim a ⟧ f2 D2 = L2 -> ⟦ lim a ⟧ f3 (D1 ⋂ D2) = (L1 + L2).
  Proof.
    intros H1 [_ H2] [_ H3]. split; auto.
    intros ε H4. specialize (H2 (ε / 2) ltac:(lra)) as [δ1 [H5 H6]].
    specialize (H3 (ε / 2) ltac:(lra)) as [δ2 [H7 H8]]. set (δ := Rmin δ1 δ2).
    assert (δ > 0) as H9 by (unfold δ; solve_min). exists δ. split. lra.
    intros x H10. assert (0 < |x - a| < δ1 /\ 0 < |x - a| < δ2) as [H11 H12] by (unfold δ in H10; solve_min).
    assert (H13 : (val (D1 ⋂ D2) x) ∈ D1). { destruct x as [val [prop1 prop2]]. autoset. }
    assert (H14 : (val (D1 ⋂ D2) x) ∈ D2). { destruct x as [val [prop1 prop2]]. autoset. }
    destruct x as [x' prop]. set (x'' := mkRsub D1 x' H13). set (x''' := mkRsub D2 x'' H14).
    specialize (H6 x'' H11). specialize (H8 x''' H12).
    assert (f3 ({| val := x'; prop := prop |}) = f1 x'' + f2 x''') as H2.
    {
      unfold f3, f_plus'. simpl. replace (f1 {| val := x'; prop := proj1 (proj1 (In_Intersection_def ℝ D1 D2 x') prop) |}) with (f1 x'').
      2 : { apply f_subtype_independent. } replace (f2 {| val := x'; prop := proj2 (proj1 (In_Intersection_def ℝ D1 D2 x') prop) |}) with (f2 x''').
      2 : { apply f_subtype_independent. } reflexivity.
    }
    rewrite H2. apply lemma_1_20; auto.
  Qed.
  
End limit_with_two_domains.