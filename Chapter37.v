Require Import Imports Limit Continuity Sets Reals_util Notations Functions.
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
  Let f := Continuity.module_37_3.f.
  Let A : Ensemble ℝ := ℝ − ⦃0, 1⦄.

  Lemma lemma_37_3_a : forall a,
    continuous_at A f a.
  Proof.
    intros [a propa]; unfold continuous_at; simpl.
    assert (a <> 0 /\ a <> 1) as [H1 H2].
    { apply In_Setminus_def in propa as [_ H1]. split; intros H2; apply H1; autoset. }
    split; admit.
  Admitted.  
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