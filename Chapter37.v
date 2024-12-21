Require Import Imports Limit Continuity Sets Reals_util Notations Functions Completeness.
Require Export Chapter36.
Import SetNotations.

Lemma lemma_37_1 : continuous_at sqrt 9.
Proof.
  unfold continuous_at; simpl. solve_lim.
Qed.

Lemma lemma_37_2 : forall f a L1 L2,
  ⟦ lim a ⟧ f = L1 -> ⟦ lim a ⟧ f = L2 -> L1 = L2. 
Proof.
  intros f a L1 L2 H1 H2.
  apply limit_of_function_unique with (f := f) (a := a); auto.
Qed.

Section section_37_3.
  Import Continuity.module_37_3.

  Let A : Ensemble ℝ := ℝ − ⦃0, 1⦄.

  Lemma lemma_37_3_a' : continuous_on A f.
  Proof.
    intros a H1. unfold continuous_at. assert (a <> 0 /\ a <> 1) as [H2 H3].
    { apply In_Setminus_def in H1 as [_ H1]. split; intros H2; apply H1; autoset. } unfold limit.
    intros ε H4. exists (Rmin (|a|/2) (|a-1|/2)). split. solve_R. intros x H5.
      assert ((a < 0 \/ 1 < a) \/ (0 < a < 1)) as [H6 | H6] by lra.
      -- assert (f a = 0 /\ f x = 0) as [H7 H8] by (split; apply f_spec; solve_R). solve_R.
      -- assert (f a = 1 /\ f x = 1) as [H7 H8] by (split; apply f_spec; solve_R). solve_R.
  Qed.

End section_37_3.

Lemma lemma_37_4 : forall f1 f2 a L1 L2,
  L1 = 0 -> L2 = 0 -> ⟦ lim a ⟧ f1 = L1 -> ⟦ lim a ⟧ f2 = L2 -> ⟦ lim a ⟧ (f1 ∙ f2) = L1 * L2.
Proof.
  intros f1 f2 a L1 L2 H1 H2 H3 H4. apply limit_mult; auto.
Qed.

Lemma lemma_37_4' : forall f1 f2 a L1 L2,
  L1 = 0 -> L2 = 0 -> ⟦ lim a ⟧ f1 = L1 -> ⟦ lim a ⟧ f2 = L2 -> ⟦ lim a ⟧ (f1 ∙ f2) = L1 * L2.
Proof.
  intros f1 f2 a L1 L2 H1 H2 H3 H4 ε H5. specialize (H3 (sqrt ε)) as [δ1 [H6 H7]]. apply sqrt_lt_R0; auto.
  specialize (H4 (sqrt ε)) as [δ2 [H8 H9]]. apply sqrt_lt_R0; auto. exists (Rmin δ1 δ2). split. solve_R.
  intros x H10. subst. specialize (H7 x ltac:(solve_R)). specialize (H9 x ltac:(solve_R)). assert (H11 : √ε * √ε = ε) by (apply sqrt_sqrt; solve_R).
  solve_R.
Qed.

Section section_37_5.
  Variables l1 l2 : list ℝ.
  Let g := polynomial l1.
  Let h := polynomial l2.
  Let f := (g / h)%function.

  Lemma lemma_37_5 : forall a,
    h a <> 0 -> continuous_at f a.
  Proof.
    intros a H1. apply lemma_37_11_c; auto; apply theorem_37_14.
  Qed.
End section_37_5.