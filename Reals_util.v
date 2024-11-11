Require Import Imports.

Open Scope R_scope.

Ltac break_INR :=
  repeat match goal with
  | [ |- context[INR (?n + ?m)] ] =>
      rewrite plus_INR
  | [ |- context[INR (?n * ?m)] ] =>
      rewrite mult_INR
  | [ |- context[INR (S ?n)] ] =>
      rewrite S_INR
  | [ |- context[INR (?n - ?m)] ] =>
      rewrite minus_INR
  end.

Ltac break_INR_simpl :=
  break_INR; simpl; try field_simplify; try nra; try nia.

Ltac convert_nat_to_INR_in_H :=
  try
  match goal with
  | [ H: (?x > ?y)%nat |- _ ] => apply lt_INR in H; simpl in H
  | [ H: (?x < ?y)%nat |- _ ] => apply lt_INR in H; simpl in H
  | [ H: (?x >= ?y)%nat |- _ ] => apply le_INR in H; simpl in H
  | [ H: (?x <= ?y)%nat |- _ ] => apply le_INR in H; simpl in H
  | [ H: (?x = ?y)%nat |- _ ] => apply INR_eq in H; simpl in H
  end.

Ltac solve_INR :=
  convert_nat_to_INR_in_H; try field_simplify_eq; try break_INR; simpl; try field; try nra; try lia.

Ltac solve_abs := 
  try intros; repeat unfold Rabs in *; repeat destruct Rcase_abs in *; try nra; try field; try nia.

Ltac solve_max := 
  try intros; repeat unfold Rmax in *; repeat destruct Rle_dec in *; try nra; try field; try nia.

Lemma pow2_gt_0 : forall r, r <> 0 -> r ^ 2 > 0.
Proof.
  intros r H1. pose proof Rtotal_order r 0 as [H2 | [H2 | H2]]; try nra.
Qed.