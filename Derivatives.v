Require Import Imports Sets Notations Functions Limit Continuity Reals_util.
Import SetNotations.

Definition differentiable_at (f:R -> R) (a:R) :=
  exists L, ⟦ lim 0 ⟧ (fun h => (f (a + h) - f a) / h) = L.

Definition differentiable_on (f:R -> R) (A:Ensemble R) :=
  forall a, a ∈ A -> differentiable_at f a.

Definition differentiable (f:R -> R) :=
  differentiable_on f (Full_set R).

Lemma lemma_9_1 : forall f a,
  ⟦ lim 0 ⟧ (fun h => (f (a + h) - f a)) = 0 <-> ⟦ lim a ⟧ f = f a.
Proof.
  intros f a. split; intros H1 ε H2.
  - specialize (H1 ε H2) as [δ [H3 H4]]. exists δ. split; auto. intros x H5.
    specialize (H4 (x - a) ltac:(solve_R)). replace (a + (x - a)) with x in H4; solve_R.
  - specialize (H1 ε H2) as [δ [H3 H4]]. exists δ. split; auto. intros x H5.
    specialize (H4 (a + x) ltac:(solve_R)). replace (a + x - a) with x in H4; solve_R.
Qed.

Theorem theorem_9_1 : forall f a,
  differentiable_at f a -> continuous_at f a.
Proof.
  intros f a [L H1]. apply lemma_9_1.
  assert (⟦ lim 0 ⟧ (fun h => (f (a + h) - f a) / h * h) = 0) as H2.
  { replace 0 with (L * 0) at 2 by lra. apply limit_mult. 2 : { apply limit_id. } auto. }
  
  apply limit_mult with (f1 := fun h => (f (a + h) - f a) / h * h) (L1 := 0) in H1.
  replace (fun h => (f (a + h) - f a) / h * h) with (fun h => (f (a + h) - f a)) in H2.
  2 : { extensionality h. field. }
Qed.