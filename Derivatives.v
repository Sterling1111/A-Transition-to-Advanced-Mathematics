Require Import Imports Sets Notations Functions Limit Continuity Reals_util.
Import SetNotations IntervalNotations.

Definition differentiable_at (f:R -> R) (a:R) :=
  exists L, ⟦ lim 0 ⟧ (fun h => (f (a + h) - f a) / h) = L.

Definition differentiable_on (f:R -> R) (A:Ensemble R) :=
  forall a, a ∈ A -> differentiable_at f a.

Definition differentiable (f:R -> R) :=
  differentiable_on f (Full_set R).

Definition derivative_at (f f' : R -> R) (a : R) :=
  ⟦ lim 0 ⟧ (fun h => (f (a + h) - f a) / h) = f' a.

Definition derivative_On (f f' : R -> R) (A : Ensemble R) :=
  forall x, x ∈ A -> derivative_at f f' x.

Definition derivative (f f' : R -> R) :=
  derivative_On f f' (Full_set R).

Notation "⟦ 'der' a ⟧ f = f'" := (derivative_at f f' a)
  (at level 70, f at level 0, no associativity, format "⟦  'der'  a  ⟧  f  =  f'").

Notation "⟦ 'der' ⟧ f = f'" := (derivative f f')
  (at level 70, f at level 0, no associativity, format "⟦  'der'  ⟧  f  =  f'").

Lemma lemma_9_1 : forall f a,
  ⟦ lim 0 ⟧ (fun h => (f (a + h) - f a)) = 0 <-> ⟦ lim a ⟧ f = f a.
Proof.
  intros f a. split; intros H1 ε H2.
  - specialize (H1 ε H2) as [δ [H3 H4]]. exists δ. split; auto. intros x H5.
    specialize (H4 (x - a) ltac:(solve_R)). replace (a + (x - a)) with x in H4; solve_R.
  - specialize (H1 ε H2) as [δ [H3 H4]]. exists δ. split; auto. intros x H5.
    specialize (H4 (a + x) ltac:(solve_R)). replace (a + x - a) with x in H4; solve_R.
Qed.

Theorem theorem_9_1 : forall f a,
  differentiable_at f a -> continuous_at f a.
Proof.
  intros f a [L H1]. apply lemma_9_1.
  assert (⟦ lim 0 ⟧ (fun h => (f (a + h) - f a) / h * h) = 0) as H2.
  { replace 0 with (L * 0) at 2 by lra. apply limit_mult. 2 : { apply limit_id. } auto. }
  apply limit_to_0_equiv with (f1 := fun h => (f (a + h) - f a) / h * h); auto.
  intros x H3. field. auto.
Qed.

Theorem theorem_10_1 : forall c,
  ⟦ der ⟧ (fun _ => c) = (fun _ => 0).
Proof.
  intros c. intros x H1. apply limit_to_0_equiv with (f1 := fun h => 0); solve_lim.
Qed.

Theorem theorem_10_2 : ⟦ der ⟧ (fun x => x) = (fun _ => 1).
Proof.
  intros x H1. apply limit_to_0_equiv with (f1 := fun h => 1); solve_lim.
Qed.

Theorem theorem_10_3_a : forall f g f' g' a,
  ⟦ der a ⟧ f = f' -> ⟦ der a ⟧ g = g' ->
  ⟦ der a ⟧ (f + g) = f' + g'.
Proof.
  intros f g f' g' a H1 H2. unfold derivative_at. 
  replace (fun h => (f (a + h) + g (a + h) - (f a + g a)) / h) with
  (fun h => (f (a + h) - f a) / h + (g (a + h) - g a) / h) by (extensionality h; nra).
  apply limit_plus; auto.
Qed.

Theorem theorem_10_3_b : forall f g f' g',
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' ->
  ⟦ der ⟧ (f + g) = f' + g'.
Proof.
  intros f g f' g' H1 H2 x H3. apply theorem_10_3_a; auto.
Qed.

Theorem theorem_10_4_a : forall f g f' g' a,
  ⟦ der a ⟧ f = f' -> ⟦ der a ⟧ g = g' ->
  ⟦ der a ⟧ (f ∙ g) = f' ∙ g + f ∙ g'.
Proof.
  intros f g f' g' a H1 H2. unfold derivative_at.
  replace (fun h => (f (a + h) * g (a + h) - f a * g a) / h) with
  (fun h => f (a + h) * ((g (a + h) - g a)/h) + ((f (a + h) - f a)/h * g a)) by (extensionality h; nra).
  replace (f' a * g a + f a * g' a) with (f a * g' a + f' a * g a) by lra.
  apply limit_plus.
  - apply limit_mult; auto. assert (continuous_at (f ∘ Rplus a) 0) as H3.
    {
       apply theorem_9_1. unfold differentiable_at. unfold derivative_at in *. exists (f' a).
       replace ((λ h : ℝ, (f (a + (0 + h)) - f (a + 0)) / h)) with (λ h : ℝ, (f (a + h) - f a) / h).
       2 : { extensionality h. rewrite Rplus_0_l. rewrite Rplus_0_r. reflexivity. }
       auto.
    }
    unfold continuous_at in H3. rewrite Rplus_0_r in H3. auto.
  - apply limit_mult; auto. solve_lim.
Qed.

Theorem theorem_10_4_b : forall f g f' g',
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' ->
  ⟦ der ⟧ (f ∙ g) = f' ∙ g + f ∙ g'.
Proof.
  intros f g f' g' H1 H2 x H3. apply theorem_10_4_a; auto.
Qed.

Theorem theorem_10_5 : forall f f' a c,
  ⟦ der a ⟧ f = f' -> ⟦ der a ⟧ (c * f) = c * f'.
Proof.
  intros f f' a c H1. set (h := fun _ : ℝ => c). set (h' := fun _ : ℝ => 0).
  assert ((c * f)%function = h ∙ f) as H3 by reflexivity. rewrite H3.
  assert (⟦ der a ⟧ h = h') as H4. { apply theorem_10_1. apply Full_intro. } 
  assert (⟦ der a ⟧ (h ∙ f) = h' ∙ f + h ∙ f') as H5.
  { apply theorem_10_4_a; auto. } 
  replace (c * f')%function with (h' ∙ f + h ∙ f')%function. 2 : { extensionality x. unfold h, h'. lra. }
  auto.
Qed.

Theorem theorem_10_5' : forall f f' c,
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ (fun x => c * f x) = (fun x => c * f' x).
Proof.
  intros f f' c H1 x H2. apply theorem_10_5; auto.
Qed.

Theorem theorem_10_6 : forall a n,
  ⟦ der a ⟧ (fun x => (x^n)) = (fun x => INR n * x ^ (n - 1)).
Proof.
  intros a. induction n as [| k IH].
  - simpl. rewrite Rmult_0_l. apply theorem_10_1. apply Full_intro.
  - replace (λ x : ℝ, (x ^ S k)%R) with (λ x : ℝ, (x * x ^ k)) by (extensionality x; reflexivity).
    replace (λ x : ℝ, INR (S k) * x ^ (S k - 1))%R with (λ x : ℝ, 1 * x^k + x * (INR k * x^(k-1))).
    2 : { 
      extensionality x. replace (S k - 1)%nat with k by lia. solve_R. replace (x * INR k * x ^ (k - 1)) with (INR k * x^k).
      2 : { 
        replace (x * INR k * x ^ (k - 1)) with (INR k * (x * x ^ (k - 1))) by lra. rewrite tech_pow_Rmult.
        destruct k; solve_R. rewrite Nat.sub_0_r. reflexivity. 
      } solve_R. 
    }
    apply theorem_10_4_a; auto. apply theorem_10_2; apply Full_intro.
Qed.

Theorem power_rule : forall n,
  ⟦ der ⟧ (fun x => x^n) = (fun x => INR n * x ^ (n - 1)).
Proof.
  intros n x H1. apply theorem_10_6.
Qed.

Theorem power_rule' : forall n m,
   m = INR n -> ⟦ der ⟧ (fun x => x^n) = (fun x => m * x ^ (n - 1)).
Proof.
  intros n m H1. rewrite H1. apply power_rule.
Qed.

Lemma limit_to_0_equiv' : forall f1 f2 L,
  (exists δ, δ > 0 /\ forall x, x <> 0 -> |x| < δ -> f1 x = f2 x) -> ⟦ lim 0 ⟧ f1 = L -> ⟦ lim 0 ⟧ f2 = L.
Proof.
  intros f1 f2 L [δ1 [H1 H2]] H3 ε H4. specialize (H3 ε H4) as [δ2 [H5 H6]].
  exists (Rmin δ1 δ2). split. solve_R. intros x H7. specialize (H2 x ltac:(solve_R) ltac:(solve_R)). specialize (H6 x ltac:(solve_R)).
  solve_R.
Qed.

Theorem theorem_10_7 : forall f f' a,
  ⟦ der a ⟧ f = f' -> f a <> 0 -> ⟦ der a ⟧ (fun x => / f x) = (fun x => -1 * f' x) ∕ (fun x => f x ^ 2).
Proof.
  intros f f' a H1 H2. unfold derivative_at. assert (H3 : continuous_at f a). { apply theorem_9_1. unfold differentiable_at. exists (f' a). auto. }
  pose proof theorem_6_3_c f a H3 H2 as [δ [H4 H5]].
  apply limit_to_0_equiv' with (f1 := fun h => ((-1 * (f (a + h) - f a) / h)) * (1 / (f a * f (a + h)))).
  { exists δ. split; auto. intros x H6 H7. specialize (H5 (a + x) ltac:(solve_R)). field_simplify; repeat split; auto. }
  apply limit_mult. replace ((λ x : ℝ, -1 * (f (a + x) - f a) / x)) with ((fun x => -1) ∙ (fun x => (f (a + x) - f a) / x)).
  2 : { extensionality x. lra. } apply limit_mult; auto. apply limit_const. apply limit_inv; solve_R.
  apply limit_mult. apply limit_const. rewrite Rmult_1_r. pose proof theorem_6_2 f (Rplus a) 0 as H6. unfold continuous_at in H6.
  rewrite Rplus_0_r in H6. apply H6. solve_lim. auto.
Qed.

Theorem theorem_10_8 : forall f f' g g' a,
  ⟦ der a ⟧ f = f' -> ⟦ der a ⟧ g = g' -> g a <> 0 -> ⟦ der a ⟧ (f ∕ g) = (g ∙ f' – f ∙ g') ∕ (g ∙ g).
Proof.
  intros f f' g g' a H1 H2 H3.
  replace (f ∕ g)%function with (f ∙ (fun x => / g x))%function. 2 : { extensionality x. unfold Rdiv. reflexivity. }
  replace (λ x : ℝ, (g x * f' x - f x * g' x) / (g x * g x)) with (fun x => (f' x * /g x + (f x * ((-1 * g' x) * / (g x)^2)))).
  2 : { extensionality x. assert (g x = 0 \/ g x <> 0) as [H4 | H4] by lra. rewrite H4. simpl. unfold Rdiv. repeat rewrite Rmult_0_l. rewrite Rinv_0. nra. field; lra. }
  apply theorem_10_4_a; auto. apply theorem_10_7; auto.
Qed.

Theorem quotient_rule : forall f g f' g',
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> (forall x, g x <> 0) -> ⟦ der ⟧ (f ∕ g) = (g ∙ f' – f ∙ g') ∕ (g ∙ g).
Proof.
  intros f g f' g' H1 H2 H3 x H4. apply theorem_10_8; auto.
Qed.

Theorem theorem_10_9 : forall f g f' g' a,
  ⟦ der a ⟧ g = g' -> ⟦ der (g a) ⟧ f = f' -> ⟦ der a ⟧ (f ∘ g) = (f' ∘ g) ∙ g'.
Proof.
  intros f g f' g' a H1 H2.
  set ( φ := fun h : ℝ => match (Req_dec (g (a + h) - g a) 0) with 
                          | left _ => f' (g a)
                          | right _ => (f (g (a + h)) - f (g a)) / (g (a + h) - g a)
                          end).
  assert (continuous_at φ 0) as H3.
  {
    intros ε H4. specialize (H2 ε H4) as [δ' [H5 H6]].  unfold φ. rewrite Rplus_0_r, Rminus_diag.
    assert (H7 : continuous_at g a). { apply theorem_9_1. unfold differentiable_at. unfold derivative_at in H1. exists (g' a). auto. }
    specialize (H7 δ' H5) as [δ [H8 H9]]. exists δ. split; auto. intros x H10.
    destruct (Req_dec (g (a + x) - g a) 0) as [H11 | H11]; destruct (Req_dec 0 0) as [H12 | H12]; try lra; clear H12.
     - solve_R. 
     - specialize (H9 (a + x) ltac:(solve_R)). specialize (H6 (g (a + x) - g a) ltac:(solve_R)).
       replace (g a + (g (a + x) - g a)) with (g (a + x)) in H6 by lra. auto.
  }
  unfold continuous_at in H3. unfold derivative_at.
  apply limit_to_0_equiv with (f1 := fun h => φ h * ((g (a + h) - g a)/h)). 
  2 : { apply limit_mult; auto. unfold φ in H3 at 2. rewrite Rplus_0_r in H3. replace (g a - g a) with 0 in H3 by lra.
         destruct (Req_dec 0 0); auto; lra. }
  intros x H4. unfold φ. destruct (Req_dec (g (a + x) - g a) 0) as [H5 | H5].
  - rewrite H5. field_simplify; auto. replace (0 / x) with 0 by nra. replace (g (a + x)) with (g a) by lra. lra.
  - field. auto.
Qed.

Theorem chain_rule : forall f g f' g',
  ⟦ der ⟧ g = g' -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ (f ∘ g) = (f' ∘ g) ∙ g'.
Proof.
  intros f g f' g' H1 H2 x H3. apply theorem_10_9; auto. specialize (H2 (g x) ltac:(apply Full_intro)). auto. 
Qed.

Example example_d1 : ⟦ der ⟧ (fun x => x^3) = (fun x => 3 * x^2).
Proof.
  apply power_rule' with (m := 3). simpl; lra.
Qed.

Definition maximum_point (f: ℝ -> ℝ) (A : Ensemble ℝ) (x : ℝ) :=
  x ∈ A /\ forall y, y ∈ A -> f y <= f x.

Definition minimum_point (f: ℝ -> ℝ) (A : Ensemble ℝ) (x : ℝ) :=
  x ∈ A /\ forall y, y ∈ A -> f x <= f y.

Definition maximum_value (f: ℝ -> ℝ) (A : Ensemble ℝ) (y : ℝ) :=
  exists x, maximum_point f A x /\ y = f x.

Definition minimum_value (f: ℝ -> ℝ) (A : Ensemble ℝ) (y : ℝ) :=
  exists x, minimum_point f A x /\ y = f x.

Definition local_maximum_point (f: ℝ -> ℝ) (A : Ensemble ℝ) (x : ℝ) :=
  x ∈ A /\ ∃ δ, δ > 0 /\ maximum_point f (A ⋂ ⦅x - δ, x + δ⦆) x.

Definition local_minimum_point (f: ℝ -> ℝ) (A : Ensemble ℝ) (x : ℝ) :=
  x ∈ A /\ ∃ δ, δ > 0 /\ minimum_point f (A ⋂ ⦅x - δ, x + δ⦆) x.

Lemma continuous_exists_min_max : forall f a b,
  a < b -> continuous_on f [a, b] -> exists y1 y2, maximum_value f [a, b] y1 /\ minimum_value f [a, b] y2.
Proof.
  intros f a b H1 H2. pose proof theorem_7_3 f a b H1 H2 as [x1 [H3 H4]]. pose proof theorem_7_7 f a b H1 H2 as [x2 [H5 H6]].
  exists (f x1), (f x2). split; unfold minimum_value, minimum_point, maximum_value, maximum_point.
  - exists x1. repeat split; unfold In in *; try lra. intros h H7. specialize (H4 h H7). lra.
  - exists x2. repeat split; unfold In in *; try lra. intros h H7. specialize (H6 h H7). lra.
Qed.

Lemma min_max_val_eq : forall f a b y1 y2,
  maximum_value f [a, b] y1 -> minimum_value f [a, b] y2 -> y1 = y2 -> forall x, x ∈ [a, b] -> f x = y1.
Proof.
  intros f a b y1 y2 H1 H2 H3 x H4. destruct H1 as [x1 [H5 H6]]. destruct H2 as [x2 [H7 H8]].
  destruct H5 as [H5 H9]. destruct H7 as [H7 H10].
  assert (f x <= y1) as H11. { specialize (H10 x H4). specialize (H9 x H4). lra. }
  assert (f x >= y1) as H12. { rewrite H3. specialize (H10 x H4). lra. }
  lra.
Qed.

Lemma min_max_val_eq' : forall f a b y1 y2,
  maximum_value f [a, b] y1 -> minimum_value f [a, b] y2 -> y1 = y2 -> forall x1 x2, x1 ∈ [a, b] -> x2 ∈ [a, b] -> f x1 = f x2.
Proof.
  intros f a b y1 y2 H1 H2 H3 x1 x2 H4 H5. specialize (min_max_val_eq f a b y1 y2 H1 H2 H3 x1 H4) as H6.
  specialize (min_max_val_eq f a b y1 y2 H1 H2 H3 x2 H5) as H7. lra.
Qed.

Theorem theorem_11_1_a : forall f a b x,
  maximum_point f ⦅a, b⦆ x -> differentiable_at f x -> ⟦ der x ⟧ f = (λ _, 0).
Proof.
  intros f a b x [H1 H2] [L H3]. assert (exists δ, 0 < δ /\ forall h, |h| < δ -> f (x + h) - f x <= 0) as [δ1 [H4 H5]].
  { exists (Rmin (b - x) (x - a)). split. unfold In in *. solve_R. intros h H4. specialize (H2 (x + h) ltac:(unfold In in *; solve_R)). lra. }
  assert (exists δ, 0 < δ /\ forall h, |h| < δ -> h > 0 -> (f (x + h) - f x) / h <= 0) as [δ2 [H6 H7]].
  { exists δ1. split. unfold In in *; solve_R. intros h H6 H7. specialize (H5 h ltac:(solve_R)) as [H8 | H8]. apply Rlt_le. apply Rdiv_neg_pos; auto. solve_R. }
  assert (exists δ, 0 < δ /\ forall h, |h| < δ -> h < 0 -> (f (x + h) - f x) / h >= 0) as [δ3 [H8 H9]].
  { exists δ1. split. unfold In in *; solve_R. intros h H10 H11. specialize (H5 h ltac:(solve_R)) as [H12 | H12]. apply Rgt_ge. apply Rdiv_neg_neg; auto. solve_R. }
  assert (L = 0 \/ L <> 0) as [H10 | H10] by lra.
  - intros ε H11. specialize (H3 ε H11) as [δ4 [H12 H13]]. exists δ4. split; auto. intros h H14. specialize (H13 h ltac:(solve_R)). solve_R.
  - exfalso. clear H1 H2 a b H4 H5 δ1. specialize (H3 (|L| / 2) ltac:(solve_R)) as [δ4 [H12 H13]]. set (h := Rmin (δ2/2) (Rmin (δ3/2) (δ4/2))).
    assert (h > 0) as H14 by (unfold h; solve_R). assert (-h < 0) as H15 by lra. specialize (H13 h ltac:(unfold h; solve_R)) as H13'. specialize (H13 (-h) ltac:(unfold h; solve_R)).
    specialize (H7 h ltac:(unfold h; solve_R) H14). specialize (H9 (-h) ltac:(unfold h; solve_R) H15). solve_R. 
Qed.

Theorem theorem_11_1_b : forall f a b x,
  minimum_point f ⦅a, b⦆ x -> differentiable_at f x -> ⟦ der x ⟧ f = (λ _, 0). 
Proof.
  intros f a b x [H1 H2] [L H3]. pose proof theorem_11_1_a (–f) a b x as H4. assert (⟦ der x ⟧ (– f) = (λ _ : ℝ, 0) -> ⟦ der x ⟧ f = (λ _ : ℝ, 0)) as H5.
  {
    intros H5. apply theorem_10_5 with (c := -1) in H5. replace (-1 * 0) with 0 in H5 by lra.
    replace ((λ x : ℝ, -1 * - f x)) with (λ x : ℝ, f x) in H5. 2 : { extensionality x'. lra. } auto.
  }
  apply H5. apply H4; auto. unfold maximum_point. split; auto. intros y H6. specialize (H2 y H6). lra.
  unfold differentiable_at. exists (-1 * L). replace ((λ h : ℝ, (- f (x + h) - - f x) / h)) with ((λ h : ℝ, -1 * ((f (x + h) - f x) / h))).
  2 : { extensionality x'. lra. } apply limit_mult; solve_lim.
Qed.

Theorem theorem_11_2_a : forall f a b x,
  local_maximum_point f ⦅a, b⦆ x -> differentiable_at f x -> ⟦ der x ⟧ f = (λ _, 0).
Proof.
  intros f a b x [H1 [δ [H2 H3]]] H4. assert (H5 : maximum_point f (⦅a - δ, b + δ⦆) x).
  { split. unfold In in *. lra. intros y H5. apply H3. replace ((λ x0 : ℝ, a < x0 < b) ⋂ λ x0 : ℝ, x - δ < x0 < x + δ) with (⦅ Rmax a (x - δ), Rmin b (x + δ) ⦆).
    2 : { apply set_equal_def. intros x0. split; intros H6. unfold In in *; split; unfold In in *; solve_R. apply In_Intersection_def in H6 as [H6 H7]. unfold In in *. solve_R. }
    unfold In in *. admit.
  }
  apply theorem_11_1_a with (a := a) (b := b); auto.
Admitted.

Definition critical_point (f: ℝ -> ℝ) (A : Ensemble ℝ) (x : ℝ) :=
  x ∈ A /\ ⟦ der x ⟧ f = (λ _, 0).

Definition critical_value (f: ℝ -> ℝ) (A : Ensemble ℝ) (y : ℝ) :=
  exists x, critical_point f A x /\ y = f x.

Theorem theorem_11_3 : forall f a b,
  a < b -> continuous_on f [a, b] -> differentiable_on f ⦅a, b⦆ -> f a = f b -> exists x, critical_point f ⦅a, b⦆ x.
Proof.
  intros f a b H1 H2 H3 H4. pose proof continuous_exists_min_max f a b H1 H2 as [y1 [y2 [H5 H6]]].
  pose proof H5 as H5'. pose proof H6 as H6'. destruct H5' as [x1 [[H7 H8] H9]]. destruct H6' as [x2 [[H10 H11] H12]].
  assert (x1 ∈ ⦅a, b⦆ \/ x2 ∈ ⦅a, b⦆ \/ ((x1 = a \/ x1 = b) /\ (x2 = a \/ x2 = b))) as [H13 | [H13 | [H13 H14]]] by (unfold In in *; lra).
  - exists x1. split; auto. apply theorem_11_1_a with (a := a) (b := b); auto. unfold maximum_value in H5. unfold maximum_point. split; auto. intros y H14. apply H8. unfold In in *. lra.
  - exists x2. split; auto. apply theorem_11_1_b with (a := a) (b := b); auto. unfold minimum_point. split; auto. intros y H14. apply H11. unfold In in *. lra.
  - assert (y1 = y2) as H15. { destruct H13 as [H13 | H13], H14 as [H14 | H14]; subst; auto. }
    pose proof min_max_val_eq' f a b y1 y2 H5 H6 H15 as H16. 
    exists ((a + b) / 2). split. unfold In. lra. apply limit_to_0_equiv' with (f1 := (fun x => 0)); try solve_lim.
    exists ((b - a)/2); split; try lra. intros h H17 H18. replace (f ((a + b) / 2 + h)) with (f ((a + b) / 2)).
    2 : { apply H16; unfold In in *; solve_R. } nra.
Qed.

Theorem theorem_11_4 : forall f a b,
  a < b -> continuous_on f [a, b] -> exists x, x ∈ ⦅a, b⦆ /\ ⟦ der x ⟧ f = (λ _, (f b - f a) / (b - a)).
Proof.
  intros f a b H1 H2. set (h := fun x => f x - ((f b - f a) / (b - a)) * (x - a)).
  assert (continuous_on h [a, b]) as H3 by admit.
  assert (differentiable_on h ⦅a, b⦆) as H4 by admit.
  assert (h a = f a) as H5 by (unfold h; lra).
  assert (h b = f a) as H6 by (unfold h; solve_R).
  pose proof theorem_11_3 h a b H1 H3 H4 ltac:(lra) as [x [H7 H8]].
  exists x; split; auto. pose proof H8 as H9.
  unfold h in H8. rewrite <- H5. unfold h.
  apply theorem_11_3 with (a := a) (b := b) in H3 as [x [H7 H8]]; solve_R.
  - exists x; split; auto. unfold derivative_at in *. unfold h in H8.
Admitted.