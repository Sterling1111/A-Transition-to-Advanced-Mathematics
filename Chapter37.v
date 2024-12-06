Require Import Imports Limit Continuity Sets.
Require Export Chapter36.
Import SetNotations.

Notation In := Coq.Sets.Ensembles.In.

Section section_37_1.
  Let Rnonneg : Ensemble R := fun x => x >= 0.

  Lemma H1 : 9 ∈ Rnonneg.
  Proof.
    unfold Rnonneg. unfold In. lra.
  Qed.

  Definition sqrt : Rsub (Rnonneg) -> R := fun x => sqrt x.
  Notation "√ x" := (sqrt x) (format "√ x", at level 20).

  Lemma lemma_37_1 : continuous_at _ sqrt (mkRsub Rnonneg 9 H1).
  Proof.
    unfold continuous_at, sqrt; simpl. split.
    - exists 8, 10. split; try lra. intros x H2. unfold Rnonneg, In in *; lra.
    - intros ε H1. exists (ε^2). split.
      + unfold Rnonneg, In. lra.
      + intros x H3. unfold Rnonneg, In in H3. apply sqrt_lt_1 in H3. lra.
  Qed.
    
End section_37_1.