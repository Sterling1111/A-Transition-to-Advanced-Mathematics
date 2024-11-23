Require Import Imports Limit.

Open Scope R_scope.

Ltac solve_lim :=
  match goal with
  | [ |- ⟦ lim ?a ⟧ ?f = ?rhs ] =>
    set (b := mkRsub (Full_set R) a ltac:(apply Full_intro));
    let result := eval cbv beta in (f b) in
    replace rhs with result by (simpl; lra); simpl; clear b;
    repeat first [ apply limit_mult | apply limit_div; try lra | apply limit_plus | apply limit_minus | apply limit_const | apply limit_id ]
  end.

Lemma lemma_36_1 : ⟦ lim 4 ⟧ (fun x => 2 * x + 3) = 11.
Proof. solve_lim. Qed.

Lemma lemma_36_2 : forall a c d, 
  ⟦ lim a ⟧ (fun x => c * x + d) = c * a + d.
Proof. intros; solve_lim. Qed.

Lemma lemma_36_3 : ⟦ lim 5 ⟧ (fun x => x^2 + 3 * x + 3) = 43.
Proof. solve_lim. Qed.

Lemma lemma_36_4 : ⟦ lim 2 ⟧ (fun x => (7 * x + 4) / (4 * x + 1)) = 2.
Proof.
  replace 2 with ((7 * 2 + 4) / (4 * 2 + 1)) at 1 by lra.
  replace ()

  replace 2 with ((7 * 2 + 4) / (4 * 2 + 1)) at 2 by lra.
  apply limit_div; try lra.
  - apply limit_plus. apply limit_mult. apply limit_const. apply limit_id. apply limit_const.
  - apply limit_plus. apply limit_mult. apply limit_const. apply limit_id. apply limit_const.
Qed.

Lemma lemma_36_5 : ⟦ lim 3 ⟧ (fun x => x^3 + x^2 + 2) = 38.
Proof. solve_lim. Qed.