Require Import Imports Limit Sums Reals_util Sets Notations Functions Completeness.
Import SetNotations IntervalNotations.

Open Scope interval_scope.

Definition continuous_at (f : ℝ -> ℝ) (a : ℝ) : Prop :=
  ⟦ lim a ⟧ f = f a.

Definition continuous_on (D : Ensemble ℝ) (f : ℝ -> ℝ) : Prop :=
  ∀ a : ℝ, a ∈ D -> continuous_at f a.

Example example_37_2 : forall c d,
  continuous_on ℝ (fun x => c * x + d).
Proof.
  intros c d a H1. unfold continuous_at. solve_lim.
Qed.

Module module_37_3.
  Definition f (x : R) : R :=
    match Rle_dec 0 x, Rle_dec x 1 with
    | left _, left _ => 1
    | _, _ => 0
    end.

  Lemma f_spec : forall x,
    ((0 <= x <= 1)%R -> f x = 1) /\ ((x < 0 \/ x > 1)%R -> f x = 0).
  Proof.
    intros x. split. 
    - intros [H1 H2]. unfold f. destruct (Rle_dec 0 x), (Rle_dec x 1); simpl in *; lra.
    - intros [H1 | H1]; unfold f; destruct (Rle_dec 0 x), (Rle_dec x 1); simpl in *; lra.
  Qed.

  Example example_37_3 : ~ continuous_at f 1.
  Proof.
    intros H1. specialize (H1 (1/2) ltac:(lra) ) as [δ [H2 H3]]. set (x := 1 + δ/2).
    specialize (H3 x ltac:(unfold x; solve_abs)). replace (f x) with 0 in H3 by (unfold f, x; solve_R).
    replace (f 1) with 1 in H3 by (unfold f; solve_R). solve_R.
  Qed.
End module_37_3.

Lemma lemma_37_11_a : forall f g a,
  continuous_at f a -> continuous_at g a -> continuous_at (f + g) a.
Proof.
  intros f g a H1 H2. unfold continuous_at in *. apply limit_plus; auto.
Qed.

Lemma lemma_37_11_b : forall f g a,
  continuous_at f a -> continuous_at g a -> continuous_at (f ∙ g) a.
Proof.
  intros f g a H1 H2. unfold continuous_at in *. apply limit_mult; auto.
Qed.

Lemma lemma_37_11_c : forall f g a,
  g a ≠ 0 -> continuous_at f a -> continuous_at g a -> continuous_at (f / g) a.
Proof.
  intros f g a H1 H2 H3. unfold continuous_at in *. apply limit_div; auto.
Qed.

Definition polynomial (l : list R) : R -> R :=
  fun x => sum_f 0 (length l - 1) (fun i => nth i l 0 * x^(length l - 1 - i)).

Lemma poly_nil : forall x, polynomial [] x = 0.
Proof.
  intro; compute. rewrite Rmult_1_r. reflexivity.
Qed.

Lemma poly_cons : forall h t x, polynomial (h :: t) x = h * x^(length t) + polynomial t x.
Proof.
  intros h t x. unfold polynomial. assert (length t = 0 \/ length t > 0)%nat as [H1 | H1] by lia.
  - rewrite length_zero_iff_nil in H1. subst; simpl; repeat rewrite sum_f_0_0; lra.
  - replace (length (h :: t) - 1)%nat with (length t) by (simpl; lia). rewrite sum_f_nth_cons_8; try lia.
    replace (x ^ (length t - 0) * h) with (h * x ^ (length t)). 2 : { rewrite Nat.sub_0_r; lra. }
    apply Rplus_eq_compat_l. apply sum_f_equiv; try lia. intros k H2.
    replace (length t - (k + 1))%nat with (length t - 1 - k)%nat by lia. reflexivity.
Qed.

Theorem theorem_37_14 : forall l a,
  continuous_at (polynomial l) a.
Proof.
  intros l a. induction l as [| h t IH].
  - unfold continuous_at. rewrite poly_nil. replace (polynomial []) with (fun _ : ℝ => 0).
    2 : { extensionality x. rewrite poly_nil. reflexivity. } solve_lim.
  - replace (polynomial (h :: t)) with (fun x : ℝ => h * x^(length t) + polynomial t x).
    2 : { extensionality x. rewrite poly_cons. reflexivity. } unfold continuous_at. solve_lim. 
Qed.

Lemma poly_c_example : continuous_on ℝ (fun x => 5*x^5 + 4*x^4 + 3*x^3 + 2*x^2 + x + 1).
Proof.
  replace (fun x : ℝ => 5 * x ^ 5 + 4 * x ^ 4 + 3 * x ^ 3 + 2 * x ^ 2 + x + 1) with (polynomial [5; 4; 3; 2; 1; 1]).
  2 : { extensionality x. compute; lra. } unfold continuous_on. intros a H1. apply theorem_37_14.
Qed.

Theorem theorem_6_1_a : forall f g a,
  continuous_at f a -> continuous_at g a -> continuous_at (f + g) a.
Proof.
  intros f g a H1 H2. unfold continuous_at in *; solve_lim.
Qed.

Theorem theorem_6_1_b : forall f g a,
  continuous_at f a -> continuous_at g a -> continuous_at (f ∙ g) a.
Proof.
  intros f g a H1 H2. unfold continuous_at in *; solve_lim.
Qed.

Theorem theorem_6_1_c : forall f a,
  f a ≠ 0 -> continuous_at f a -> continuous_at (fun x => 1 / f x) a.
Proof.
  intros f a H1 H2. unfold continuous_at in *; solve_lim.
Qed.

Theorem theorem_6_1_d : forall f g a,
  g a ≠ 0 -> continuous_at f a -> continuous_at g a -> continuous_at (f / g) a.
Proof.
  intros f g a H1 H2 H3. unfold continuous_at in *; solve_lim.
Qed.

Theorem theorem_6_2 : forall f g a,
  continuous_at g a -> continuous_at f (g a) -> continuous_at (f ∘ g) a.
Proof.
  intros f g a H1 H2 ε H3. unfold continuous_at in *. specialize (H2 ε H3) as [δ1 [H4 H5]].
  specialize (H1 δ1 H4) as [δ2 [H6 H7]]. exists δ2. split; auto. intros x H8.
  specialize (H7 x H8). specialize (H5 (g x)). pose proof classic (g x = g a) as [H9 | H9].
  - rewrite H9. solve_R.
  - specialize (H5 ltac:(solve_R)). auto.
Qed.

Theorem theorem_6_3_a : ∀ f a,
  continuous_at f a -> f a > 0 -> ∃ δ, δ > 0 /\ ∀ x, |x - a| < δ -> f x > 0.
Proof.
  intros f a H1 H2. specialize (H1 (f a) H2) as [δ [H3 H4]]. exists δ. split; auto.
  intros x H5. pose proof classic (x = a) as [H6 | H6].
  - subst. auto.
  - specialize (H4 x ltac:(solve_R)). solve_R.
Qed.

Theorem theorem_6_3_b : ∀ f a,
  continuous_at f a -> f a < 0 -> ∃ δ, δ > 0 /\ ∀ x, |x - a| < δ -> f x < 0.
Proof.
  intros f a H1 H2. specialize (H1 (-f a) ltac:(lra)) as [δ [H3 H4]]. exists δ. split; auto.
  intros x H5. pose proof classic (x = a) as [H6 | H6].
  - subst. auto.
  - specialize (H4 x ltac:(solve_R)). solve_R.
Qed.

Theorem theorem_7_1 : forall f a b,
  a < b -> continuous_on [a, b] f -> f a < 0 < f b -> ∃ x, x ∈ [a, b] /\ f x = 0.
Proof.
  intros f a b H1 H2 H3.
  set (A := (fun x1 => x1 ∈ [a, b] /\ ∀ x2, x2 ∈ [a, x1] -> f x2 < 0)).
  assert (H4 : A ≠ ∅).
  { apply not_Empty_In. exists a. split. unfold In. lra. intros x H4. unfold In in H4. replace x with a by lra. lra. }
  assert (H5 : is_upper_bound A b). { intros x H5. unfold A, In in H5. destruct H5 as [H5 H6]. specialize (H6 b). lra. }
  assert (H6 : has_upper_bound A). { exists b. auto. }
  destruct (completeness_upper_bound A H6 H4) as [α H7]. assert (H8 : a < α < b).
  { destruct H7 as [H7 H8]. unfold is_lub in H7. destruct H7 as [H7 H8]. unfold In in H7. lra. }
  { destruct H7 as [H7 _]. unfold is_lub in H7. destruct H7 as [H7 H8]. unfold In in H7. lra. }
  assert (H7 : a < α < b).
  { destruct H6 as [H6 H7]. unfold is_lub in H6. destruct H6 as [H6 H7]. unfold In in H6. lra. }
  { destruct H6 as [H6 _]. unfold is_lub in H6. destruct H6 as [H6 H7]. unfold In in H6. lra. }
  pose proof Rtotal_order (f α) 0 as [H7 | [H7 | H7]].
  - assert (H8 : continuous_at f α). { unfold continuous_on in H2. specialize (H2 α). apply H2. unfold In. destruct H6 as [H6 H6']. specialize (H6' b). ltac:(solve_R)). lra. }
    pose proof theorem_6_3_a f α H8 H7 as [δ [H9 H10]]. exists α. split; auto. unfold In. split; auto.
    intros x H11. unfold In in H11. specialize (H10 x ltac:(solve_R)). lra.
  pose proof theorem_6_3_b f α. H6 H7 as [δ [H8 H9]]. exists α. split; auto. unfold In. split; auto.
    intros x H10. unfold In in H10. specialize (H9 x ltac:(solve_R)). lra.
Admitted.

Theorem theorem_7_4 : forall f a b c,
  continuous_on [a, b] f -> f a < c < f b -> ∃ x, x ∈ [a, b] /\ f x = c.
Proof.
Admitted.