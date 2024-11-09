Require Import Imports Fibonacci WI_SI_WO.
Require Export Chapter14.

Open Scope nat_scope.

Notation In := List.In.

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

  Lemma max_fib_le_n : forall n,
    n > 0 -> exists i, F i <= n < F (S i).
  Proof.
    intros n H1. assert (n = 1 \/ n = 2 \/ n = 3 \/ n > 3) as [H2 | [H2 | [H2 | H2]]] by lia;
    [exists 1 | exists 2 | exists 3 |]; try (simpl; lia). clear H1. rename H2 into H1.
    set (E i := F i > n). assert (exists i, E i) as H2. { exists n. unfold E. apply fib_n_gt_n; auto. }
    pose proof WI_SI_WO as [_ [_ WO]]. apply WO in H2 as [i [H2 H3]].
    exists (i - 1). assert (i = 0 \/ i > 0) as [H4 | H4] by lia.
    - rewrite H4 in H2. unfold E in H2. simpl in H2. lia.
    - split.
      -- unfold E in H2. pose proof classic (F (i -1) <= n) as [H5 | H5]; auto.
         apply not_le in H5. specialize (H3 (i - 1) H5). lia.
      -- replace (S (i - 1)) with i by lia. unfold E in H2. auto.
  Qed.
  
  Lemma fold_right_plus_nat_In : forall l n,
    In n l -> n <= fold_right plus 0 l.
  Proof.
    intros l n H1. induction l as [| h t IH].
    - inversion H1.
    - destruct H1 as [H1 | H1].
      -- simpl; lia.
      -- simpl. specialize (IH H1). lia.
  Qed.

  Lemma lemma_15_7 : forall n,
    n > 0 -> exists l, NoDup l /\ n = fold_right plus 0 (map F l).
  Proof.
    intros n. strong_induction n. intros H1.
    pose proof (max_fib_le_n n ltac : (lia)) as [i H2].
    assert (F i = n \/ F i < n) as [H3 | H3] by lia.
    - exists [i]. split. constructor; auto. constructor. simpl. lia.
    - assert (F i > 0) as H4 by (apply fib_nat_gt_0). specialize (IH (n - F i) ltac:(lia) ltac:(lia)) as [l [H5 H6]].
      exists ([i] ++ l). split. 2 : { rewrite map_app. rewrite fold_right_plus_app_nat. simpl. lia. }
      apply NoDup_cons; auto. intros H7. assert (fold_right plus 0 (map F l) >= F i) as H8.
      { apply in_map with (f := F) in H7. apply fold_right_plus_nat_In; auto. }
      assert (n >= F i + F i) as H9 by lia. assert (i > 1) as H10.
      { destruct i. simpl in H2. lia. destruct i. simpl in H2, H3. lia. lia. }
      assert (F i > F (i - 1)) as H11.
      { 
        replace i with (S (i - 1)) by lia. rewrite fib_S_n_nat; try lia.
        replace (S (i - 1) - 1)%nat with (i - 1)%nat by lia. 
        pose proof (fib_nat_gt_0 (i - 1 - 1)) as H11. unfold F. lia. 
      }
      assert (F i + F i > F (S i)) as H12. { rewrite fib_S_n_nat; unfold F in *; lia. }
      lia.
  Qed.
  
End section_15_7.