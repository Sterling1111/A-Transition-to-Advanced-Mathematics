Require Import Imports Limit Sets Notations Functions Reals_util.
Require Export Chapter35.
Import SetNotations.

Lemma lemma_36_1 : ⟦ lim 4 ⟧ (fun x => 2 * x + 3) = 11.
Proof.
  intros ε H1. exists (ε/2). split. apply Rdiv_pos_pos. lra. lra. intros x H2.
  solve_R.
Qed.

Lemma lemma_36_1' : ⟦ lim 4 ⟧ (fun x => 2 * x + 3) = 11.
Proof. solve_lim. Qed.

Lemma lemma_36_2 : forall a c d, ⟦ lim a ⟧ (fun x => c * x + d) = c * a + d.
Proof.
  intros a c d. intros ε H1. assert (c = 0 \/ c <> 0) as [H2 | H2] by lra.
  - exists 1. split; solve_R.
  - exists (ε / Rabs c). split. apply Rdiv_pos_pos; solve_R. intros x [H3 H4].
    replace (c * x + d - (c * a + d)) with (c * (x - a)) by lra. 
    apply Rmult_lt_compat_r with (r := Rabs c) in H4; field_simplify in H4; solve_R.
Qed.

Lemma lemma_36_2' : forall a c d, ⟦ lim a ⟧ (fun x => c * x + d) = c * a + d.
Proof. intros. solve_lim. Qed.

Lemma lemma_36_3 :  ⟦ lim 5 ⟧ (fun x => x^2 + 3 * x + 3) = 43.
Proof.
  intros ε H1. exists (Rmin 1 (ε/14)). split. solve_R. intros x H2.
  replace (x^2 + 3 * x + 3 - 43) with ((x - 5) * (x + 8)) by lra.
  solve_R.
Qed.

Lemma lemma_36_3' : ⟦ lim 5 ⟧ (fun x => x^2 + 3 * x + 3) = 43.
Proof. solve_lim. Qed.

Lemma lemma_36_4 : ⟦ lim 2 ⟧ (fun x => (7 * x + 4) / (4 * x + 1)) = 2.
Proof. solve_lim. Qed.

Lemma lemma_36_5 : ⟦ lim 3 ⟧ (fun x => x^3 + x^2 + 2) = 38.
Proof.
  intros ε H1. exists (Rmin 1 (ε/44)). split. solve_R. intros x [H2 H3].
  replace (x^3 + x^2 + 2 - 38) with ((x - 3) * (x^2 + 4 * x + 12)) by lra.
  
  solve_R.
Admitted.

Lemma lemma_36_5' : ⟦ lim 3 ⟧ (fun x => x^3 + x^2 + 2) = 38.
Proof. solve_lim. Qed.