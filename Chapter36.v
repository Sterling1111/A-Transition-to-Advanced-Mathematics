Require Import Imports Limit Sets.
Import SetNotations.

Lemma lemma_36_1 : ⟦ lim 4 ⟧ (fun x => 2 * x + 3) = 11.
Proof.
  replace 11 with (2 * 4 + 3) by lra.
  apply limit_plus_Full_set. with (f1 := fun x => 2 * x) (f2 := fun _ => 3) (a := 4) (L1 := 2 * 4) (L2 := 3).

Lemma lemma_36_2 : forall a c d, ⟦ lim a ⟧ (fun x => c * x + d) = c * a + d.
Proof. intros; solve_lim. Qed.

Lemma lemma_36_3 : ⟦ lim 5 ⟧ (fun x => x^2 + 3 * x + 3) = 43.
Proof. solve_lim. Qed.

Lemma lemma_36_4 : ⟦ lim 2 ⟧ (fun x => (7 * x + 4) / (4 * x + 1)) = 2.
Proof. solve_lim. Qed.


Lemma lemma_36_5 : ⟦ lim 3 ⟧ (fun x => x^3 + x^2 + 2) = 38.
Proof. solve_lim. Qed.