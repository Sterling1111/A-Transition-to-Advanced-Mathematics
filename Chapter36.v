Require Import Imports Limit Sets.
Require Export Chapter35.
Import SetNotations.

Lemma lemma_36_1 : ⟦ lim 4 ⟧ (fun x => 2 * x + 3) = 11.
Proof. apply limit_iff_limit'. solve_lim. Qed.

Lemma lemma_36_2 : forall a c d, ⟦ lim a ⟧ (fun x => c * x + d) = c * a + d.
Proof. intros; solve_lim. Qed.

Lemma lemma_36_3 : ⟦ lim 5 ⟧ (fun x => x^2 + 3 * x + 3) = 43.
Proof. solve_lim. Qed.

Lemma lemma_36_4 : ⟦ lim 2 ⟧ (fun x => (7 * x + 4) / (4 * x + 1)) = 2.
Proof. solve_lim. Qed.

Lemma lemma_36_5 : ⟦ lim 3 ⟧ (fun x => x^3 + x^2 + 2) = 38.
Proof. solve_lim. Qed.