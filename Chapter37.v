Require Import Imports Limit Continuity Sets Reals_util Notations Functions.
Require Export Chapter36.
Import SetNotations.

Section section_37_1.
  Lemma H1 : 9 ∈ Full_set ℝ.
  Proof. apply Full_intro. Qed.

  Lemma lemma_37_1_helper : forall x, √x - 3 = (x-9) / (√x+3).
  Proof.
    intros x. 
  Admitted.



  Lemma lemma_37_1 : continuous_at ℝ sqrt (mkRsub ℝ 9 H1).
  Proof.
    unfold continuous_at. simpl. split; try apply Full_set_encloses.
    intros ε H1. exists (ε^2). split; try (simpl; nra).
    intros [x prop] [H2 H3]; simpl in *. replace 9 with (3 * 3) by lra. rewrite sqrt_square; try lra.
         rewrite lemma_37_1_helper. Search (|_ / _|).
         assert (x <> 3 * 3) as H4 by solve_abs. assert (√x <> 3).
         { intros H5. apply H4. apply sqrt_inj; try lra. inversion prop; lra. rewrite sqrt_square; auto; lra. }
         apply Rlt_pow_base with (n := 2%nat); try lra; try lia. solve_abs.
         simpl. 
         apply sqrt_lt_1_alt. lra.
  Qed.
    
End section_37_1.