Require Import Imports Limit Continuity Sets Reals_util Notations Functions Completeness.
Require Export Chapter36.
Import SetNotations.

Lemma lemma_37_1 : continuous_at ℝ sqrt (mkRsub ℝ 9 ltac:(apply Full_intro)).
Proof.
  unfold continuous_at; simpl. unfold Type_to_Ensemble. solve_lim.
Qed.

Lemma lemma_37_2 : forall f a L1 L2,
  ⟦ lim a ⟧ f = L1 -> ⟦ lim a ⟧ f = L2 -> L1 = L2. 
Proof.
  intros f a L1 L2 H1 H2. apply limit_iff_limit' in H1, H2. 
  apply limit_of_function_unique with (D := Full_set R) (f := f) (a := a); auto.
Qed.

Section section_37_3.
  Import Continuity.module_37_3.

  Let A : Ensemble ℝ := ℝ − ⦃0, 1⦄.

  Lemma lemma_37_3_a' : continuous_on A f.
  Proof.
    intros [a H1]. unfold continuous_at. simpl. assert (a <> 0 /\ a <> 1) as [H2 H3].
    { apply In_Setminus_def in H1 as [_ H1]. split; intros H2; apply H1; autoset. } unfold limit. split.
    - assert (a < 0 \/ 1 < a \/ 0 < a < 1) as [H4 | [H4 | H4]] by lra;
      [ exists (a-1), (a/2) | exists ((a+1)/2), (a+1) | exists(a/2), ((a+1)/2) ]; split; try lra; intros x H5;
      unfold A; unfold Ensembles.In in H5; rewrite In_Setminus_def; split; 
      first [apply Full_intro | intros H6; destruct_finite_set H6; lra].
    - intros ε H4. exists (Rmin (|a|/2) (|a-1|/2)). split. solve_R. intros [x H5] H6; simpl in *.
      assert ((a < 0 \/ 1 < a) \/ (0 < a < 1)) as [H7 | H7] by lra.
      -- assert (f a = 0 /\ f x = 0) as [H8 H9] by (split; apply f_spec; solve_R). solve_R.
      -- assert (f a = 1 /\ f x = 1) as [H8 H9] by (split; apply f_spec; solve_R). solve_R.
  Qed.

  Lemma lemma_37_3_a : forall a : (Rsub (Full_set ℝ)),
    a ∈ A -> continuous_at (Full_set R) f a.
  Proof.
    intros [a H1] H2; unfold continuous_at; simpl in *; split; try apply Full_set_encloses.
    intros ε H3. assert (a <> 0 /\ a <> 1) as [H4 H5].
    { apply In_Setminus_def in H2 as [_ H2]. split; intros H4; apply H2; autoset. }
    exists (Rmin (|a|/2) (|a-1|/2)). split. solve_R. intros [x H6] H7; simpl in *.
    assert ((a < 0 \/ 1 < a) \/ (0 < a < 1)) as [H8 | H8] by lra.
    - assert (f a = 0 /\ f x = 0) as [H9 H10] by (split; apply f_spec; solve_R). solve_R.
    - assert (f a = 1 /\ f x = 1) as [H9 H10] by (split; apply f_spec; solve_R). solve_R.
  Qed.
End section_37_3.

Lemma lemma_37_4 : forall D f1 f2 a L1 L2,
  L1 = 0 -> L2 = 0 -> encloses D a -> ⟦ lim a ⟧ f1 D = L1 -> ⟦ lim a ⟧ f2 D = L2 -> ⟦ lim a ⟧ ((f1 ∙ f2)%f) D = L1 * L2.
Proof.
  intros D f1 f2 a L1 L2 H1 H2 H3 H4 H5. apply limit_mult; auto.
Qed.

Section section_37_5.
  Variables l1 l2 : list ℝ.
  Let g := polynomial' l1.
  Let h := polynomial' l2.
  Let f := (g / h)%f.

  Lemma lemma_37_5 : forall a,
    h a <> 0 -> continuous_at ℝ f a.
  Proof.
    intros a H1. apply lemma_37_11_c; auto; apply theorem_37_14.
  Qed.
End section_37_5.