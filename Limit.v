Require Import Imports Sequence Sets Chapter12 Reals_util Sequence Notations.
Import SetNotations.

Open Scope R_scope.

Definition encloses (D : Ensemble R) (a : R) : Prop :=
  exists b c, b < a < c /\ (fun x => b <= x <= c) ⊆ D.

Record Rsub (D : Ensemble R) := mkRsub {
  x :> R;
  cond : x ∈ D
}.

Definition limit (D : Ensemble R) (f : Rsub D -> R) (a L : R) : Prop :=
  encloses D a /\
    (∀ ε, ε > 0 ⇒ ∃ δ, δ > 0 /\ ∀ x : Rsub D, 0 < |x - a| < δ ⇒ |f x - L| < ε).

Notation "⟦ 'lim' a ⟧ f '=' L" := 
  (limit (Full_set ℝ) f a L) 
    (at level 70, f at level 0, no associativity, format "⟦  'lim'  a  ⟧  f  '='  L").

Notation "⟦ 'lim' a ⟧ f D '=' L" := 
  (limit D f a L) 
    (at level 70, f at level 0, D at level 0, no associativity, format "⟦  'lim'  a  ⟧  f  D  '='  L").

Lemma Full_set_encloses : forall a, encloses (Full_set ℝ) a.
Proof.
  intros a. exists (a - 1), (a + 1). split. lra. intros x _. apply Full_intro.
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

Infix "+" := f_plus : f_scope.
Notation "- x" := (f_opp x) : f_scope.
Infix "∙" := f_mult (at level 40) : f_scope.
Infix "-" := f_minus : f_scope.
Infix "/" := f_div : f_scope.
Infix "^" := f_pow (at level 30) : f_scope.
Infix "*" := f_mult_c : f_scope.
Notation "/ x" := (f_inv x) : f_scope.
Notation "f1 'o' f2" := (f_comp f1 f2)
  (at level 20, right associativity) : f_scope.

Lemma limit_of_function_unique' : forall D f a L1 L2,
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

Lemma limit_of_function_unique : forall f a L1 L2,
  ⟦ lim a ⟧ f = L1 -> ⟦ lim a ⟧ f = L2 -> L1 = L2.
Proof.
  intros f a L1 L2 H1 H2. apply (limit_of_function_unique' (Full_set ℝ) f a L1 L2); auto.
Qed.

Lemma limit_plus : forall f1 f2 a L1 L2,
  ⟦ lim a ⟧ f1 = L1 -> ⟦ lim a ⟧ f2 = L2 -> ⟦ lim a ⟧ ((f1 + f2)%f) = (L1 + L2).
Proof.
  intros f1 f2 a L1 L2 [_ H1] [_ H2]. split.
  - apply Full_set_encloses.
  - intros ε H3. specialize (H1 (ε / 2) ltac:(lra)) as [δ1 [H4 H5]].
    specialize (H2 (ε / 2) ltac:(lra)) as [δ2 [H6 H7]]. set (δ := Rmin δ1 δ2).
    assert (δ > 0) as H8 by (unfold δ; solve_min). exists δ. split. lra.
    intros x H9. assert (0 < |x - a| < δ1 /\ 0 < |x - a| < δ2) as [H10 H11] by (unfold δ in H9; solve_min).
    specialize (H5 x H10). specialize (H7 x H11). apply lemma_1_20; auto.
Qed.

Theorem Rsub_Full_set_equiv : @eq Type (Rsub (Full_set R)) R.
Proof.
  apply univalence. exists (fun x => x). exists (fun x => mkRsub (Full_set R) x ltac:(apply Full_intro)).
  split.
  - intros x. destruct x; simpl. replace (cond0) with (Full_intro R x0); auto.
    destruct cond0. apply proof_irrelevance.
  - intros y. reflexivity.
Qed.

Lemma limit_const : forall a c,
  ⟦ lim a ⟧ (fun _ => c) = c.
Proof.
  intros a c. split; try apply Full_set_encloses. intros ε H1. exists 1. split; solve_abs.
Qed.

Lemma limit_id : forall a,
  ⟦ lim a ⟧ (fun x => x) = a.
Proof.
  intros a. split; try apply Full_set_encloses. intros ε H1. exists ε. split; solve_abs.
Qed.

Lemma f_minus_plus : forall (f1 f2 : Rsub (Full_set R) -> R),
  (f1 - f2 = f1 + (- f2)%f)%f.
Proof.
  intros f1 f2. apply functional_extensionality. intros x. unfold f_minus, f_plus, f_opp. lra.
Qed.

Lemma limit_minus : forall f1 f2 a L1 L2,
  ⟦ lim a ⟧ f1 = L1 -> ⟦ lim a ⟧ f2 = L2 -> ⟦ lim a ⟧ ((f1 - f2)%f) = L1 - L2.
Proof.
   intros f1 f2 a L1 L2 H1 [_ H2]. rewrite f_minus_plus. unfold Rminus. apply limit_plus; auto.
   split; try apply Full_set_encloses. intros ε H3. specialize (H2 ε H3) as [δ [H4 H5]].
   exists δ. split; auto. intros x H6. apply H5 in H6. unfold f_opp. solve_abs.
Qed.

Lemma limit_mult : forall f1 f2 a L1 L2,
  ⟦ lim a ⟧ f1 = L1 -> ⟦ lim a ⟧ f2 = L2 -> ⟦ lim a ⟧ ((f1 ∙ f2)%f) = L1 * L2.
Proof.
  intros f1 f2 a L1 L2 [_ H1] [_ H2]. split.
  - apply Full_set_encloses.
  - intros ε H3. assert (ε / (2 * ((|L2|) + 1)) > 0 /\ ε / (2 * ((|L1|) + 1)) > 0) as [H4 H5].
    { split; apply Rdiv_pos_pos; solve_abs. }
    specialize (H1 (Rmin (ε / (2 * ((|L2|) + 1))) 1) ltac:(solve_min)) as [δ1 [H6 H7]].
    specialize (H2 (ε / (2 * ((|L1|) + 1))) ltac:(solve_min)) as [δ2 [H8 H9]].
    set (δ := Rmin δ1 δ2). assert (δ > 0) as H10 by (unfold δ; solve_min). exists δ. split. lra.
    intros x H11. assert (0 < |x - a| < δ1 /\ 0 < |x - a| < δ2) as [H12 H13] by (unfold δ in H11; solve_min).
    specialize (H7 x H12). specialize (H9 x H13).
    apply lemma_1_21; auto.
Qed.

Lemma limit_inv : forall f a L,
  ⟦ lim a ⟧ f = L -> L <> 0 -> ⟦ lim a ⟧ ((/ f)%f) = / L.
Proof.
  intros f a L [_ H1] H2. split.
  - apply Full_set_encloses.
  - intros ε H3. assert (|L| / 2 > 0) as H4 by solve_abs. assert (ε * |L|^2 / 2 > 0) as H5.
    { apply Rmult_lt_0_compat. apply pow2_gt_0 in H2. solve_abs. apply Rinv_pos; lra. }
    specialize (H1 (Rmin (|L| / 2) (ε * |L|^2 / 2)) ltac:(solve_min)) as [δ [H6 H7]].
    exists δ. split. lra. intros x H8. specialize (H7 x H8). repeat rewrite <- Rdiv_1_l. unfold f_inv.
    rewrite <- Rdiv_1_l. apply lemma_1_22; auto.
Qed.

Lemma limit_div : forall f1 f2 a L1 L2,
  ⟦ lim a ⟧ f1 = L1 -> ⟦ lim a ⟧ f2 = L2 -> L2 <> 0 -> ⟦ lim a ⟧ ((f1 / f2)%f) = L1 / L2.
Proof.
  intros f1 f2 a L1 L2 H1 H2 H3. replace (f1 / f2)%f with (f1 ∙ (f_inv f2))%f by reflexivity.
  unfold Rdiv. apply limit_mult; auto. apply limit_inv; auto.
Qed.

Lemma limit_pow : forall f a L n,
  ⟦ lim a ⟧ f = L ⇒ ⟦ lim a ⟧ ((f ^ n)%f) = L ^ n.
Proof.
  intros f a L n H1. induction n as [| n IH].
  - rewrite pow_O. replace ((fun x0 : Rsub (Full_set ℝ) => f x0 ^ 0)) with (fun x0 : Rsub (Full_set ℝ) => 1).
    2 : { extensionality x. rewrite pow_O. reflexivity. } apply limit_const.
  - simpl. apply limit_mult; auto.
Qed.

Lemma lim_equality_substitution : forall f a L1 L2,
  L1 = L2 -> ⟦ lim a ⟧ f = L1 -> ⟦ lim a ⟧ f = L2.
Proof.
  intros f a L1 L2 H1 [_ H2]. split.
  - apply Full_set_encloses.
  - intros ε H3. specialize (H2 ε H3) as [δ [H4 H5]].
    exists δ; split; auto. intros x. specialize (H5 x). solve_abs.
Qed.

Ltac solve_lim :=
  try solve_R;
  match goal with
  | [ |- ⟦ lim ?a ⟧ ?f = ?rhs ] =>
    let b :=
      match type of a with
      | R => constr:(mkRsub (Full_set R) a ltac:(apply Full_intro))
      | _ => constr:(a)
      end in
    let L2' := eval cbv beta in (f b) in
    let L2 := eval simpl in L2' in
    let H := fresh "H" in 
    assert (⟦ lim a ⟧ f = L2) as H by 
    (repeat first [ 
                     apply limit_div
                     | apply limit_pow
                     | apply limit_mult
                     | apply limit_inv
                     | apply limit_plus
                     | apply limit_minus
                     | apply limit_const
                     | apply limit_id
                     | solve_R
                 ]);
    apply (lim_equality_substitution f a L2 rhs); solve_R
  end.
