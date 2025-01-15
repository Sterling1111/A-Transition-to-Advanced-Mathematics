Require Import Imports Limit Sums Reals_util Sets Notations Functions Completeness.
Import SetNotations IntervalNotations.

Open Scope interval_scope.

Definition continuous_at (f : ℝ -> ℝ) (a : ℝ) : Prop :=
  ⟦ lim a ⟧ f = f a.

Definition continuous_on (f : ℝ -> ℝ) (D : Ensemble ℝ) : Prop :=
  ∀ a : ℝ, a ∈ D -> continuous_at f a.

Definition uniformly_continuous_on (f : ℝ -> ℝ) (a b : ℝ) : Prop :=
  ∀ ε, ε > 0 -> ∃ δ, δ > 0 /\ ∀ x y, x ∈ [a, b] -> y ∈ [a, b] -> |x - y| < δ -> |f x - f y| < ε.

Definition continuous (f : ℝ -> ℝ) : Prop :=
  continuous_on f (Full_set ℝ).

Example example_37_2 : forall c d,
  continuous_on (fun x => c * x + d) ℝ.
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
  g a ≠ 0 -> continuous_at f a -> continuous_at g a -> continuous_at (f ∕ g) a.
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

Lemma poly_c_example : continuous_on (fun x => 5*x^5 + 4*x^4 + 3*x^3 + 2*x^2 + x + 1) ℝ.
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
  g a ≠ 0 -> continuous_at f a -> continuous_at g a -> continuous_at (f ∕ g) a.
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

Theorem theorem_6_3_c : ∀ f a,
  continuous_at f a -> f a ≠ 0 -> ∃ δ, δ > 0 /\ ∀ x, |x - a| < δ -> f x ≠ 0.
Proof.
  intros f a H1 H2. assert (f a > 0 \/ f a < 0) as [H3 | H3] by lra.
  - apply theorem_6_3_a in H3 as [δ [H4 H5]]; auto. exists δ. split; auto.
    intros x H6. specialize (H5 x ltac:(solve_R)). lra.
  - apply theorem_6_3_b in H3 as [δ [H4 H5]]; auto. exists δ. split; auto.
    intros x H6. specialize (H5 x ltac:(solve_R)). lra.
Qed.

Lemma lemma_6_16_a_1 : ∀ f a,
  ⟦ lim a⁺ ⟧ f = f a -> f a > 0 -> ∃ δ, δ > 0 /\ (∀ x, 0 <= x - a < δ -> f x > 0).
Proof.
  intros f a H1 H2. specialize (H1 (f a) H2) as [δ [H3 H4]]. exists δ. split; auto.
  intros x H5. assert (x = a \/ x > a) as [H6 | H6] by lra.
  - subst. auto.
  - specialize (H4 x ltac:(solve_R)). solve_R.
Qed.

Lemma lemma_6_16_a_2 : ∀ f a,
  ⟦ lim a⁺ ⟧ f = f a -> f a < 0 -> ∃ δ, δ > 0 /\ (∀ x, 0 <= x - a < δ -> f x < 0).
Proof.
  intros f a H1 H2. specialize (H1 (-f a) ltac:(lra)) as [δ [H3 H4]]. exists δ. split; auto.
  intros x H5. assert (x = a \/ x > a) as [H6 | H6] by lra.
  - subst. auto.
  - specialize (H4 x ltac:(solve_R)). solve_R.
Qed.

Lemma lemma_6_16_b_1 : ∀ f a,
  ⟦ lim a⁻ ⟧ f = f a -> f a > 0 -> ∃ δ, δ > 0 /\ (∀ x, 0 <= a - x < δ -> f x > 0).
Proof.
  intros f a H1 H2. specialize (H1 (f a) H2) as [δ [H3 H4]]. exists δ. split; auto.
  intros x H5. assert (x = a \/ x < a) as [H6 | H6] by lra.
  - subst. auto.
  - specialize (H4 x ltac:(solve_R)). solve_R.
Qed.

Lemma lemma_6_16_b_2 : ∀ f a,
  ⟦ lim a⁻ ⟧ f = f a -> f a < 0 -> ∃ δ, δ > 0 /\ (∀ x, 0 <= a - x < δ -> f x < 0).
Proof.
  intros f a H1 H2. specialize (H1 (-f a) ltac:(lra)) as [δ [H3 H4]]. exists δ. split; auto.
  intros x H5. assert (x = a \/ x < a) as [H6 | H6] by lra.
  - subst. auto.
  - specialize (H4 x ltac:(solve_R)). solve_R.
Qed.

Theorem theorem_7_1 : forall f a b,
  a < b -> continuous_on f [a, b] -> f a < 0 < f b -> ∃ x, x ∈ [a, b] /\ f x = 0.
Proof.
  intros f a b H1 H2 H3.
  set (A := (fun x1 => x1 ∈ [a, b] /\ ∀ x2, x2 ∈ [a, x1] -> f x2 < 0)).
  assert (H4' : forall x, x ∈ A -> forall x2, a <= x2 <= x -> x2 ∈ A).
  {
    intros x H4 x2 H5. destruct H4 as [H4 H6]. unfold A, In. split. unfold In in H4. lra. 
    intros x3 H7. apply H6. split; try lra.
  }
  assert (H4 : a ∈ A). { unfold A. split. unfold In. lra. intros x H4. unfold In in H4. replace x with a by lra. lra. }
  assert (H5 : A ≠ ∅). { apply not_Empty_In. exists a. auto. }
  assert (H6 : is_upper_bound A b). { intros x H6. unfold A, In in H6. lra. }
  assert (H7 : has_upper_bound A). { exists b. auto. }
  destruct (completeness_upper_bound A H7 H5) as [α H8].
  assert (H9 : α < b).
  {
    specialize (H2 b ltac:(unfold In; lra)). unfold continuous_at in H2. apply left_right_iff in H2 as [H2 _].
    pose proof lemma_6_16_b_1 f b H2 ltac:(lra) as [δ [H10 H11]]. set (x := Rmax a (b - δ/2)).
    assert (H12 : is_upper_bound A x).
    { 
      intros x1 H12. unfold A, In in H12. destruct H12 as [H12 H13].
      assert (x1 <= x \/ x1 > x) as [H14 | H14] by lra; auto. specialize (H13 x ltac:(split; [ unfold x |]; solve_R)).
      specialize (H11 x ltac:(unfold x; solve_R)). lra. 
    }
    assert (H13 : x < b). { unfold x. solve_R. } destruct H8 as [H8 H14]. specialize (H8 a H4). specialize (H14 x H12). lra.
  }
  assert (H10 : a < α).
  {
    specialize (H2 a ltac:(unfold In; lra)). unfold continuous_at in H2. apply left_right_iff in H2 as [_ H2].
    pose proof lemma_6_16_a_2 f a H2 ltac:(lra) as [δ2 [H10 H11]]. set (x := Rmin b (a + δ2/2)).
    assert (H12 : x ∈ A).
    {
      unfold A. split. unfold x, In. solve_R. intros x2 H12. specialize (H11 x2). apply H11. unfold x, In in H12. solve_R.
    }
    assert (H13 : x > a). { unfold x. solve_R. } destruct H8 as [H8 H14]. specialize (H8 x H12). lra. 
  }
  pose proof Rtotal_order (f α) 0 as [H11 | [H11 | H11]]; [ exfalso | | exfalso].
  - assert (H12 : continuous_at f α). { unfold continuous_on in H2. specialize (H2 α). apply H2. unfold In. lra. }
    pose proof theorem_6_3_b f α H12 H11 as [δ [H13 H14]]. 
    assert (exists x0, x0 ∈ A /\ α - δ < x0 < α) as [x0 [H15 H16]].
    {
      assert (α ∈ A \/ α ∉ A) as [H15 | H15] by apply classic.
      - exists (Rmax a (α - δ/2)). split.
        -- apply H4' with (x := α); solve_R.
        -- solve_R.
      - pose proof classic (∃ x0 : ℝ, x0 ∈ A ∧ α - δ < x0 < α) as [H16 | H16]; auto.
        assert (H17 : forall x, α - δ < x < α -> x ∉ A).
        { intros x H17 H18. destruct H18 as [H18 H19]. apply H16. exists x. split; auto. unfold A, In. split; solve_R. }
        assert (H18 : is_upper_bound A (α - δ)).
        {
          intros x H18. assert (x <= α - δ \/ x > α - δ) as [H19 | H19] by lra; auto. destruct H8 as [H8 _]. specialize (H8 x H18).
          assert (x = α \/ x < α) as [H20 | H20] by lra. subst. tauto. specialize (H17 x ltac:(lra)). tauto.
        }
        destruct H8 as [_ H8]. specialize (H8 (α - δ) H18). lra.
    }
    assert (forall x, x ∈ [a, x0] -> f x < 0) as H17.
    { intros x H17. unfold A in H15. destruct H15 as [H15 H18]. specialize (H18 x H17). lra. }
    set (x := Rmin b (α + δ / 2)). assert (H18 : x ∈ A).
    {
      unfold A, In, x; split. solve_R. intros x2 H18.
      assert (a <= x2 <= x0 \/ x0 < x2 <= Rmin b (α + δ / 2)) as [H19 | H19] by lra.
      - apply H17. auto.
      - apply H14. solve_R.
    }
    assert (x > α) as H19. { unfold x. solve_R. } destruct H8 as [H8 _]. specialize (H8 x H18). lra.
  - exists α. unfold In. split; lra.
  - assert (H12 : continuous_at f α). { unfold continuous_on in H2. specialize (H2 α). apply H2. unfold In. lra. }
    pose proof theorem_6_3_a f α H12 H11 as [δ [H13 H14]]. 
    assert (exists x0, x0 ∈ A /\ α - δ < x0 < α) as [x0 [H15 H16]].
    {
      assert (α ∉ A) as H15.
      { intros H15. unfold A, In in H15. destruct H15 as [_ H15]. specialize (H15 α ltac:(lra)). lra. }
      pose proof classic (∃ x0 : ℝ, x0 ∈ A ∧ α - δ < x0 < α) as [H16 | H16]; auto.
      assert (H17 : forall x, α - δ < x < α -> x ∉ A).
      { intros x H17 H18. destruct H18 as [H18 H19]. apply H16. exists x. split; auto. unfold A, In. split; solve_R. }
      assert (H18 : is_upper_bound A (α - δ)).
      {
        intros x H18. assert (x <= α - δ \/ x > α - δ) as [H19 | H19] by lra; auto. destruct H8 as [H8 _]. specialize (H8 x H18).
        assert (x = α \/ x < α) as [H20 | H20] by lra. subst. tauto. specialize (H17 x ltac:(lra)). tauto.
      }
      destruct H8 as [_ H8]. specialize (H8 (α - δ) H18). lra.
    }
    assert (forall x, x ∈ [a, x0] -> f x < 0) as H17.
    { intros x H17. unfold A in H15. destruct H15 as [H15 H18]. specialize (H18 x H17). lra. }
    assert (a <= x0) as H18. { unfold A in H15. destruct H15 as [H15 _]. unfold In in H15. lra. }
    specialize (H14 x0 ltac:(solve_R)). specialize (H17 x0). unfold In in H17. lra.
Qed.

Theorem theorem_8_1 : forall f a,
  continuous_at f a -> ∃ δ c, δ > 0 /\ ∀ x, |x - a| < δ -> f x < c.
Proof.
  intros f a H1. unfold continuous_at in H1. specialize (H1 1 ltac:(lra)) as [δ [H2 H3]].
  exists δ, (f a + 1). split; auto. intros x H4. assert (x = a \/ x ≠ a) as [H5 | H5] by apply classic.
  - subst. lra.
  - specialize (H3 x ltac:(solve_R)). solve_R.
Qed.

Lemma lemma_8_1_a : forall f a,
  ⟦ lim a⁺ ⟧ f = f a -> ∃ δ c, δ > 0 /\ ∀ x, a <= x < a + δ -> f x < c.
Proof.
  intros f a H1. specialize (H1 1 ltac:(lra)) as [δ [H2 H3]]. exists δ, (f a + 1). split; auto.
  intros x H4. assert (x = a \/ x ≠ a) as [H5 | H5] by apply classic.
  - subst. lra.
  - specialize (H3 x ltac:(solve_R)). solve_R.
Qed.

Lemma lemma_8_1_b : forall f a,
  ⟦ lim a⁻ ⟧ f = f a -> ∃ δ c, δ > 0 /\ ∀ x, a - δ < x <= a -> f x < c.
Proof.
  intros f a H1. specialize (H1 1 ltac:(lra)) as [δ [H2 H3]]. exists δ, (f a + 1). split; auto.
  intros x H4. assert (x = a \/ x ≠ a) as [H5 | H5] by apply classic.
  - subst. lra.
  - specialize (H3 x ltac:(solve_R)). solve_R.
Qed.

Theorem theorem_7_2 : forall f a b,
  a < b -> continuous_on f [a, b] -> ∃ c, ∀ x, x ∈ [a, b] -> f x < c.
Proof.
  intros f a b H1 H2. set (A := fun x => a <= x <= b /\ ∃ c, ∀ x2, x2 ∈ [a, x] -> f x2 < c).
  assert (H3 : a ∈ A). { unfold A, In. split; try lra. exists (f a + 1). intros x H3. replace x with a; lra. }
  assert (H4 : A ≠ ∅). { apply not_Empty_In. exists a. auto. }
  assert (H5 : is_upper_bound A b). { intros x H5. unfold A, In in H5. lra. }
  assert (H6 : has_upper_bound A). { exists b. auto. }
  destruct (completeness_upper_bound A H6 H4) as [α H7].
  pose proof Rtotal_order α b as [H8 | [H8 | H8]]; pose proof Rtotal_order α a as [H9 | [H9 | H9]]; subst; try lra.
  - destruct H7 as [H7 _]. specialize (H7 a H3). lra.
  - clear H8. assert (continuous_at f a) as H8. { unfold continuous_on in H2. specialize (H2 a ltac:(unfold In; lra)). auto. }
    pose proof theorem_8_1 f a H8 as [δ [c [H9 H10]]]. assert ((Rmin b (a + δ/2)) ∈ A) as H11.
    { unfold A, In. split. solve_R. exists c. intros x H11. specialize (H10 x ltac:(solve_R)). solve_R. }
    destruct H7 as [H7 _]. specialize (H7 (Rmin b (a + δ/2)) H11). solve_R.
  - assert (continuous_at f α) as H10. { unfold continuous_on in H2. specialize (H2 α ltac:(unfold In; lra)). auto. }
    pose proof theorem_8_1 f α H10 as [δ [c [H11 H12]]]. assert (exists x0, x0 ∈ A /\ α - δ < x0 < α) as [x0 [H13 H14]].
    {
      assert (α ∈ A \/ α ∉ A) as [H13 | H13] by apply classic.
      - exists (Rmax a (α - δ/2)). split.
        -- unfold A, In. destruct H13 as [H13 [c2 H14]]. split. solve_R. exists c2. intros x H15. apply H14. unfold In. solve_R.
        -- solve_R.
      - pose proof classic (∃ x0 : ℝ, x0 ∈ A /\ α - δ < x0 < α) as [H14 | H14]; auto.
        assert (H15 : forall x, α - δ < x < α -> x ∉ A).
        { intros x H15 H16. destruct H16 as [H16 H17]. apply H14. exists x. split; auto. unfold A, In. split; solve_R. }
        assert (H16 : is_upper_bound A (α - δ)).
        {
          intros x H16. assert (x <= α - δ \/ x > α - δ) as [H17 | H17] by lra; auto. destruct H7 as [H7 _]. specialize (H7 x H16).
          assert (x = α \/ x < α) as [H18 | H18] by lra. subst. tauto. specialize (H15 x ltac:(lra)). tauto.
        }
        destruct H7 as [_ H7]. specialize (H7 (α - δ) H16). lra.
    }
    assert (exists c, forall x, x ∈ [a, x0] -> f x < c) as [c2 H15].
    { destruct H13 as [H13 [c2 H16]]. exists c2. intros x H17. unfold A in H13. destruct H13 as [H13 H18]. apply H16. unfold In in H17. solve_R. }
    assert (Rmin b (x0 + δ) ∈ A) as H16.
    {
      unfold A, In. split. solve_R. exists (Rmax c c2). intros x H16. assert (x <= x0 \/ x > x0) as [H17 | H17] by lra.
      - specialize (H15 x ltac:(unfold In; lra)). solve_R.
      - specialize (H12 x ltac:(solve_R)). solve_R.
    }
    destruct H7 as [H7 _]. specialize (H7 (Rmin b (x0 + δ)) H16). solve_R.
  - clear H9. assert (continuous_at f b) as H9. { unfold continuous_on in H2. specialize (H2 b ltac:(unfold In; lra)). auto. }
    pose proof theorem_8_1 f b H9 as [δ [c [H10 H11]]]. assert (exists x0, x0 ∈ A /\ b - δ < x0 <= b) as [x0 [H12 H13]].
    {
      assert (b ∈ A \/ b ∉ A) as [H12 | H12] by apply classic.
      - exists (Rmin b (b + δ/2)). split.
        -- unfold A, In. destruct H12 as [H12 [c2 H14]]. split. solve_R. exists c2. intros x H15. apply H14. unfold In. solve_R.
        -- solve_R.
      - pose proof classic (∃ x0 : ℝ, x0 ∈ A /\ b - δ < x0 <= b) as [H13 | H13]; auto.
        assert (H14 : forall x, b - δ < x <= b -> x ∉ A).
        { intros x H14 H15. destruct H15 as [H15 H16]. apply H13. exists x. split; auto. unfold A, In. split; solve_R. }
        assert (H15 : is_upper_bound A (b - δ)).
        {
          intros x H15. assert (x <= b - δ \/ x > b - δ) as [H16 | H16] by lra; auto. destruct H7 as [H7 _]. specialize (H7 x H15).
          assert (x = b \/ x < b) as [H17 | H17] by lra. subst. tauto. specialize (H14 x ltac:(lra)). tauto.
        }
        destruct H7 as [_ H7]. specialize (H7 (b - δ) H15). lra.
    }
    assert (exists c, forall x, x ∈ [x0, b] -> f x < c) as [c2 H14].
    { destruct H12 as [H12 [c2 H15]]. exists c. intros x H16. apply H11. unfold In in *. solve_R. }
    assert (exists c, forall x, x ∈ [a, x0] -> f x < c) as [c3 H15].
    { destruct H12 as [H12 [c3 H16]]. exists c3. intros x H17. apply H16. unfold In in H17. solve_R. }
    exists (Rmax c2 c3). intros x H16. specialize (H14 x). specialize (H15 x). unfold In in *. assert (x <= x0 \/ x > x0) as [H17 | H17] by lra.
    -- specialize (H15 ltac:(solve_R)). solve_R.
    -- specialize (H14 ltac:(solve_R)). solve_R.
  - destruct H7 as [_ H7]. specialize (H7 b H5). lra.
Qed.

Theorem theorem_7_3 : forall f a b,
  a < b -> continuous_on f [a, b] -> exists x1, x1 ∈ [a, b] /\ (forall x2, x2 ∈ [a, b] -> f x1 >= f x2).
Proof.
  intros f a b H1 H2. set (A := fun x => exists y, y ∈ [a, b] /\ x = f y).
  assert (H3 : A ≠ ∅). { apply not_Empty_In. exists (f a). exists a. split; unfold In; solve_R. }
  pose proof theorem_7_2 f a b H1 H2 as [c H4]. assert (H5 : is_upper_bound A c).
  { intros x [y [H5 H6]]. specialize (H4 y H5). lra. }
  assert (H6 : has_upper_bound A). { exists c. auto. }
  destruct (completeness_upper_bound A H6 H3) as [α H7]. 
   pose proof classic (exists y, y ∈ [a, b] /\ α = f y) as [[y [H8 H9]] | H8].
  - exists y. split. solve_R. intros x H10. subst. destruct H7 as [H7 _]. specialize (H7 (f x) ltac:(exists x; split; auto)). lra.
  - exfalso. assert (H9 : forall y, y ∈ [a, b] -> f y <> α). { intros y H9 H10. apply H8. exists y. split; auto. }
    set (g := fun x => 1 / (α - f x)). assert (H10 : continuous_on g [a, b]).
    {
      unfold continuous_on. intros x H10. unfold continuous_at, g. apply limit_div.
      - apply limit_const.
      - apply limit_minus. apply limit_const. apply H2; auto.
      - intros H11. specialize (H9 x). apply H9; solve_R. 
    }
    pose proof theorem_7_2 g a b H1 H10 as [c2 H11].
    assert (H12 : forall ε, ε > 0 -> exists x, x ∈ [a, b] /\ α - f x < ε).
    {
      intros ε H12. assert (exists x0, x0 ∈ A /\ α - ε < x0 < α) as [x0 [H13 H14]].
      {
        assert (α ∈ A \/ α ∉ A) as [H13 | H13] by apply classic.
        - exists α. split. auto. solve_R.
        - pose proof classic (∃ x0, x0 ∈ A /\ α - ε < x0 < α) as [H14 | H14]; auto.
          assert (H15 : forall x, α - ε < x < α -> x ∉ A).
          { intros x H15 H16. apply H14. exists x. split; auto. }
          assert (H16 : is_upper_bound A (α - ε)).
          {
            intros x H16. assert (x <= α - ε \/ x > α - ε) as [H17 | H17] by lra; auto. destruct H7 as [H7 _]. specialize (H7 x H16).
            assert (x = α \/ x < α) as [H18 | H18] by lra. subst. tauto. specialize (H15 x ltac:(lra)). tauto.
          }
          destruct H7 as [_ H7]. specialize (H7 (α - ε) H16). lra.
      }
      destruct H13 as [y [H13 H15]]. exists y. split; auto. unfold In in *. solve_R.
    }
    assert (H13 : forall ε, ε > 0 -> exists x, x ∈ [a, b] /\ g x > ε).
    {
      intros ε H13. specialize (H12 (1/ε) ltac:(apply Rdiv_pos_pos; solve_R)) as [x [H12 H14]]. exists x. split; auto. unfold g.
      specialize (H9 x ltac:(unfold In; solve_R)). assert (α > f x) as H15.
      {
        pose proof classic (α > f x) as [H15 | H15]; auto. exfalso. apply H9. assert (f x >= α) as [H16 | H16] by lra; auto.
        assert (f x ∈ A) as H17. { exists x. split; auto. } destruct H7 as [H7 _]. specialize (H7 (f x) H17). lra. 
      }
      apply Rmult_lt_compat_l with (r := ε) in H14; solve_R.
      apply Rmult_lt_compat_l with (r := 1 / (α - f x)) in H14. field_simplify in H14; solve_R. apply Rdiv_pos_pos; lra.
    }
    specialize (H13 (Rmax c2 1) ltac:(solve_R)) as [x [H14 H15]]. specialize (H11 x H14). solve_R.
Qed.

Lemma f_continuous_neg_f_continuous : forall f a b,
  a < b -> continuous_on f [a, b] -> continuous_on (fun x => -1 * f x) [a, b].
Proof.
  intros f a b H1 H2. replace (fun x => -f x) with (fun x => -1 * f x). 2 : { extensionality x. lra. }
  unfold continuous_on. intros x H3. unfold continuous_at. apply limit_mult. apply limit_const. apply H2; auto.
Qed.

Theorem theorem_7_4 : forall f a b c,
  a < b -> continuous_on f [a, b] -> f a < c < f b -> ∃ x, x ∈ [a, b] /\ f x = c.
Proof.
  intros f a b c H1 H2 H3. (set (g := fun x => f x - c)). assert (H4 : continuous_on g [a, b]).
  {
    unfold continuous_on. intros x H4. unfold continuous_at, g. apply limit_minus. apply H2; auto.
    apply limit_const.
  }
  apply theorem_7_1 in H4 as [x [H4 H5]]; unfold g in *; solve_R. exists x; split; solve_R.
Qed.

Theorem theorem_7_5 : forall f a b c,
  a < b -> continuous_on f [a, b] -> f b < c < f a -> ∃ x, x ∈ [a, b] /\ f x = c.
Proof.
  intros f a b c H1 H2 H3. pose proof f_continuous_neg_f_continuous f a b H1 H2 as H4.
  pose proof theorem_7_4 (fun x => -1 * f x) a b (-c) H1 H4 ltac:(solve_R) as [x [H5 H6]]. exists x; split; solve_R.
Qed.

Theorem theorem_7_6 : forall f a b,
  a < b -> continuous_on f [a, b] -> exists N, forall x, x ∈ [a, b] -> f x >= N.
Proof.
  intros f a b H1 H2. pose proof f_continuous_neg_f_continuous f a b H1 H2 as H3.
  pose proof theorem_7_2 (fun x => -1 * f x) a b H1 H3 as [M H4]. exists (-M). intros x H5. specialize (H4 x H5). lra.
Qed.

Theorem theorem_7_7 : forall f a b,
  a < b -> continuous_on f [a, b] -> exists x1, x1 ∈ [a, b] /\ (forall x2, x2 ∈ [a, b] -> f x1 <= f x2).
Proof.
  intros f a b H1 H2. pose proof f_continuous_neg_f_continuous f a b H1 H2 as H3.
  pose proof theorem_7_3 (fun x => -1 * f x) a b H1 H3 as [y [H4 H5]]. exists y. split. solve_R.
  intros x H6. specialize (H5 x H6). lra.
Qed.

Lemma continuous_imp_continuous_on : forall f a b,
  continuous f -> continuous_on f [a, b].
Proof.
  intros f a b H1. unfold continuous_on. intros x H2. unfold continuous_at. apply H1. apply Full_intro.
Qed.

Theorem theorem_7_8 : forall α,
  α > 0 -> exists x, x * x = α.
Proof.
  intros α H1. set (f := fun x => x * x). assert (H2 : continuous f). { intros a H2. unfold continuous_at. solve_lim. }
  assert (α < 1 \/ α = 1 \/ α > 1) as [H3 | [H3 | H3]] by lra.
  - pose proof theorem_7_4 f 0 1 α ltac:(lra) ltac:(apply continuous_imp_continuous_on; auto) ltac:(unfold f; solve_R) as [x [H4 H5]].
    exists x. apply H5.
  - exists 1. lra.
  - pose proof theorem_7_4 f 0 α α H1  ltac:(apply continuous_imp_continuous_on; auto) ltac:(unfold f; split; solve_R) as [x [H4 H5]].
    exists x. apply H5.
Qed.

Lemma lemma_8_A_1 : forall f a b c ε,
  a < b < c -> continuous_on f [a, c] -> ε > 0 -> 
  (exists δ1, δ1 > 0 /\ forall x y, x ∈ [a, b] -> y ∈ [a, b] -> |x - y| < δ1 -> |f x - f y| < ε) ->
  (exists δ2, δ2 > 0 /\ forall x y, x ∈ [b, c] -> y ∈ [b, c] -> |x - y| < δ2 -> |f x - f y| < ε) ->
  exists δ, δ > 0 /\ forall x y, x ∈ [a, c] -> y ∈ [a, c] -> |x - y| < δ -> |f x - f y| < ε.
Proof.
  intros f a b c ε H1 H2 H3 [δ1 [H4 H5]] [δ2 [H6 H7]].
Admitted.