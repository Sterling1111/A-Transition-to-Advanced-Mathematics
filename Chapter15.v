Require Import ZArith Lia Classical Reals Lra Classical_sets List Fibonacci Sums Sets WI_SI_WO.
Require Export Chapter14.

Import ListNotations SetNotations.

Open Scope nat_scope.

Lemma lemma_15_3_a : forall n,
  n >= 14 -> exists x y, n = 3 * x + 8 * y.
Proof.
  intros n H1. strong_induction n. intros H1.
  assert (n = 14 \/ n = 15 \/ n = 16 \/ n > 16) as [H2 | [H2 | [H2 | H2]]] by lia.
  - exists 2, 1. lia.
  - exists 5, 0. lia.
  - exists 0, 2. lia.
  - assert (H3 : (n - 3 < n)) by lia. assert (H4 : (n - 3) >= 14) by lia. specialize (IH (n - 3) H3 H4).
    destruct IH as [x [y IH]]. exists (x + 1), y. lia.
Qed.

Lemma lemma_15_3_b : forall x y,
  13 <> 3 * x + 8 * y.
Proof.
  lia.
Qed.

Lemma lemma_15_4 : forall n,
  n > 0 -> exists e m, n = 2^e * m /\ Nat.Odd m.
Proof.
  intros n. strong_induction n. intros H1. destruct (Nat.Even_or_Odd n) as [[k H2] | H2].
  - assert (k < n) as H3 by lia. assert (k > 0) as H4 by lia. specialize (IH k H3 H4) as [e [m [H5 H6]]].
    exists (S e), m. simpl. split; auto; lia.
  - exists 0, n; split; auto; lia.
Qed.

Lemma lemma_15_5_a : forall n,
  n >= 44 -> exists x y z, n = 6 * x + 9 * y + 20 * z.
Proof.
  intros n H1. strong_induction n. intros H1.
  assert (n = 44 \/ n = 45 \/ n = 46 \/ n = 47 \/ n = 48 \/ n = 49 \/ n > 49) as [H2 | [H2 | [H2 | [H2 | [H2 | [H2 | H2]]]]]] by lia.
  - exists 1, 2, 1. lia.
  - exists 0, 5, 0. lia.
  - exists 1, 0, 2. lia.
  - exists 0, 3, 1. lia.
  - exists 8, 0, 0. lia.
  - exists 0, 1, 2. lia.
  - assert (H3 : (n - 6 < n)) by lia. assert (H4 : (n - 6) >= 44) by lia. specialize (IH (n - 6) H3 H4).
    destruct IH as [x [y [z IH]]]. exists (x + 1), y, z. lia.
Qed.

Lemma lemma_15_5_b : forall x y z,
  43 <> 6 * x + 9 * y + 20 * z.
Proof.
  lia.
Qed.

Lemma lemma_15_6_a : forall n,
  n >= 22 -> exists x y z, n = 4 * x + 10 * y + 15 * z.
Proof.
  intros n H1. strong_induction n. intros H1.
  assert (n = 22 \/ n = 23 \/ n = 24 \/ n = 25 \/ n > 25) as [H2 | [H2 | [H2 | [H2 | H2]]]] by lia.
  - exists 3, 1, 0. lia.
  - exists 2, 0, 1. lia.
  - exists 1, 2, 0. lia.
  - exists 0, 1, 1. lia.
  - assert (H3 : (n - 4 < n)) by lia. assert (H4 : (n - 4) >= 22) by lia. specialize (IH (n - 4) H3 H4).
    destruct IH as [x [y [z IH]]]. exists (x + 1), y, z. lia.
Qed.

Lemma lemma_15_6 : forall x y z,
  21 <> 4 * x + 10 * y + 15 * z.
Proof. lia.
Qed.

Section section_15_7.
  Local Definition F := Fibonacci.fibonacci_nat.

  Lemma fold_right_plus_app_nat : forall l1 l2,
    fold_right plus 0 (l1 ++ l2) = fold_right plus 0 l1 + fold_right plus 0 l2.
  Proof.
    induction l1 as [| h t IH]; intros l2; simpl; try lia. rewrite IH. lia.
  Qed.

  Lemma lemma_15_7 : forall n,
    n > 1 -> exists l, n = fold_right plus 0 (map F l).
  Proof.
    intros n. strong_induction n. intros H1. assert (n = 2 \/ n = 3 \/ n > 3) as [H2 | [H2 | H2]] by lia.
    - exists [1;1]. simpl. lia.
    - exists [1;2]. simpl. lia.
    - pose proof (IH (n-2) ltac:(lia) ltac:(lia)) as [l1 H3]. pose proof (IH 2 ltac:(lia) ltac:(lia)) as [l2 H4].
      exists (l1 ++ l2). rewrite map_app. rewrite fold_right_plus_app_nat. rewrite <- H3, <- H4. lia.
  Qed.
  
End section_15_7.