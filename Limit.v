Require Import Imports Sequence Sets Chapter12 Reals_util Sequence.
Import SetNotations.

Open Scope R_scope.

Notation "'∀' x , P" := (forall x, P)
  (at level 200, x ident, P at level 200, only parsing).

Notation "'∃' x , P" := (exists x, P)
  (at level 200, x ident, P at level 200).

Notation "∀ x : T , P" := (forall x : T, P)
  (at level 200, x ident, T at level 200, P at level 200, only parsing).

Notation "∃ x , P" := (exists x, P)
  (at level 200, x ident, P at level 200, only parsing).

Notation "∃ x : T , P" := (exists x : T, P)
  (at level 200, x ident, T at level 200, P at level 200, only parsing).

Definition encloses (D : Ensemble R) (a : R) : Prop :=
  exists b c, b < a < c /\ (fun x => b <= x <= c) ⊆ D.

Record Rsub (D : Ensemble R) := mkRsub {
  x :> R;
  cond : x ∈ D
}.

Definition limit (D : Ensemble R) (f : Rsub D -> R) (a : Rsub D) (L : R) : Prop :=
  encloses D a /\
    (∀ ε, ε > 0 ⇒ ∃ δ, δ > 0 /\ ∀ x : Rsub D, 0 < |x - a| < δ ⇒ |f x - L| < ε).

Notation "⟦ 'lim' a ⟧ f '=' L" := 
  (limit (Full_set ℝ) f a L) 
    (at level 70, f at level 0, no associativity, format "⟦  'lim'  a  ⟧  f  '='  L").

Notation "⟦ 'lim' a ⟧ f D '=' L" := 
  (limit D f a L) 
    (at level 70, f at level 0, D at level 0, no associativity, format "⟦  'lim'  a  ⟧  f  D  '='  L").

(*
Definition limit_pos_inf (f : ℝ -> ℝ) (L : ℝ) : Prop :=
  ∀ ε, ε > 0 ⇒
    ∃ N, ∀ x, x > N ⇒ |f x - L| < ε.

Definition limit_neg_inf (f : ℝ -> ℝ) (L : ℝ) : Prop :=
  ∀ ε, ε > 0 ⇒
    ∃ N, ∀ x, x < N ⇒ |f x - L| < ε.

Definition limit_right (f : ℝ -> ℝ) (D : Ensemble ℝ) (a L : ℝ) : Prop :=
  ∀ ε, ε > 0 ⇒
    ∃ δ, ∀ x, x ∈ D ⇒ 0 < x - a < δ ⇒ |f x - L| < ε.

Definition limit_left (f : ℝ -> ℝ) (D : Ensemble ℝ) (a L : ℝ) : Prop :=
  ∀ ε, ε > 0 ⇒
    ∃ δ, ∀ x, x ∈ D ⇒ 0 < a - x < δ ⇒ |f x - L| < ε.

Notation "⟦ 'lim' a ⟧ f D '=' L" := 
  (limit f D a L) 
  (at level 70, f at level 0, D at level 0, no associativity, format "⟦  'lim'  a  ⟧  f  D  '='  L").

Notation "⟦ 'lim' ∞ ⟧ f '=' L" := 
  (limit_pos_inf f L)
  (at level 70, f at level 0, no associativity, format "⟦  'lim' ∞  ⟧  f  '='  L").

Notation "⟦ 'lim' -∞ ⟧ f '=' L" := 
  (limit_neg_inf f L)
  (at level 70, f at level 0, no associativity, format "⟦  'lim'  -∞  ⟧  f  '='  L").

Notation "⟦ 'lim' a ⁺ ⟧ f '=' L" := 
  (limit_right f (Full_set ℝ) a L)
  (at level 70, f at level 0, no associativity, format "⟦  'lim'  a ⁺  ⟧  f  '='  L").

Notation "⟦ 'lim' a ⁻ ⟧ f '=' L" := 
  (limit_left f (Full_set ℝ) a L)
  (at level 70, f at level 0, no associativity, format "⟦  'lim'  a ⁻  ⟧  f  '='  L").

*)

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
  y0 <> 0 -> |y - y0| < Rmin (|y0 / 2|) ((ε * |y0|^2) / 2) -> y <> 0 /\ |1 / y - 1 / y0| < ε.
Proof.
  intros y y0 eps H1 H2. assert (H3 : y <> 0).
  - assert (H4 : Rabs (y - y0) < Rabs (y0 / 2)). { apply Rlt_gt in H2. apply Rmin_Rgt_l in H2. lra. } solve_abs.
  - split.
    -- apply H3.
    -- assert (H4 : Rabs (y - y0) < Rabs (y0 / 2)). { apply Rlt_gt in H2. apply Rmin_Rgt_l in H2. lra. }
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

Notation "f + g" := (fun x => f x + g x) (at level 50, left associativity) : function_scope.

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
  ⟦ lim a ⟧ f1 = L1 -> ⟦ lim a ⟧ f2 = L2 -> ⟦ lim a ⟧ (f1 + f2) = L1 + L2.
Proof.
  intros f1 f2 a L1 L2 [_ H1] [_ H2]. split.
  - exists (a-1), (a+1). split. lra. intros x _. apply Full_intro.
  - intros ε H3. specialize (H1 (ε / 2) ltac:(lra)) as [δ1 [H4 H5]].
    specialize (H2 (ε / 2) ltac:(lra)) as [δ2 [H6 H7]]. set (δ := Rmin δ1 δ2).
    assert (δ > 0) as H8 by (unfold δ; solve_min). exists δ. split. lra.
    intros x H9. assert (0 < |x - a| < δ1 /\ 0 < |x - a| < δ2) as [H10 H11] by (unfold δ in H9; solve_min).
    specialize (H5 x H10). specialize (H7 x H11). apply lemma_1_20; auto.
Qed.