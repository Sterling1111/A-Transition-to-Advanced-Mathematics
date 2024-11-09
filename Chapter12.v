Require Import Imports Sets.
Require Export Chapter11.

Import SetNotations.

Notation ℕ := nat.
Notation ℤ := Z.
Notation ℚ := Q.
Notation ℝ := R.

(* Nicer notation for logical implication *)
Notation "A ⇒ B" := (A -> B) (at level 99, right associativity) : type_scope.
(* Define notation for logical equivalence (if and only if) *)
Notation "A ⟺ B" := (A <-> B) (at level 99, no associativity) : type_scope.

Open Scope Z_scope.

Lemma lemma_12_1_a : forall (U : Type) (A B C : Ensemble U),
  A ⊆ B ⋂ C ⇒ A ⊆ B.
Proof.
  intros U A B C H1 x H2. rewrite Subset_def in H1. specialize (H1 x H2). apply In_Intersection_def in H1 as [H1 _]. auto.
Qed.

Lemma lemma_12_1_a_converse : 
  (forall (U : Type) (A B C : Ensemble U), A ⊆ B ⇒ A ⊆ B ⋂ C) ⇒ False.
Proof.
  intros H1. specialize (H1 Z ⦃1⦄ ⦃1,3⦄ ⦃2⦄).
  assert (⦃1⦄ ⊆ ⦃1, 3⦄) as H2. { intros x H2. solve_in_Intersection_Union_helper_2. }
  specialize (H1 H2). assert (⦃1⦄ ⊈ ⦃1,3⦄ ⋂ ⦃2⦄) as H3. 
  { apply not_Subset_def. exists 1. split. solve_in_Intersection_Union_helper_2. solve_not_in_ensemble. }
  auto.
Qed.

Lemma lemma_12_2 : forall (U : Type) (S T : Ensemble U),
  S ⊆ T <-> S = S ⋂ T.
Proof.
  intros U S T. split.
  - intros H1. apply set_equal_def. intros x. rewrite Subset_def in H1. specialize (H1 x). split; solve_in_Intersection_Union_helper_2.
  - intros H1. apply Subset_def. intros x H2. rewrite set_equal_def in H1. specialize (H1 x) as [H1 _]. specialize (H1 H2).
    solve_in_Intersection_Union_helper_2.
Qed.

Lemma lemma_12_3 : forall (U : Type) (S T : Ensemble U),
  S ⊆ T <-> T = S ⋃ T.
Proof.
  intros U S T. split.
  - intros H1. apply set_equal_def. intros x. rewrite Subset_def in H1. specialize (H1 x). split; solve_in_Intersection_Union_helper_2.
  - intros H1. apply Subset_def. intros x H2. rewrite set_equal_def in H1. specialize (H1 x) as [H1 H3].
    rewrite In_Union_def in H3. apply H3. left. auto.
Qed.

Lemma lemma_12_4_a : forall (U : Type) (S T : Ensemble U),
  S ⋂ T = T ⋃ S -> S = T.
Proof.
  intros U S T H1. apply set_equal_def. intros x. rewrite set_equal_def in H1. specialize (H1 x) as [H1 H2]. split; 
  intros H3; rewrite In_Union_def in H2; assert (x ∈ T \/ x ∈ S) as H4 by auto; specialize (H2 H4); solve_in_Intersection_Union_helper_2.
Qed.

Lemma lemma_12_4_b : forall (U : Type) (S T : Ensemble U),
  S × T = T × S -> S ≠ ∅ -> T ≠ ∅ -> S = T.
Proof.
  intros U S T H1 H2 H3. apply set_equal_def. intros x. split.
  - intros H4. rewrite set_equal_def in H1. apply not_Empty_In in H3 as [y H3]. specialize (H1 (x, y)) as [H1 H5].
    assert ((x, y) ∈ S × T) as H6. { exists x, y; auto. } assert ((x, y) ∈ T × S) as H7. { apply H1; auto. }
    apply In_prod_def in H7 as [H7 _]. auto.
  - intros H4. rewrite set_equal_def in H1. apply not_Empty_In in H2 as [y H2]. specialize (H1 (y, x)) as [H1 H5].
    assert ((y, x) ∈ S × T) as H6. { exists y, x; auto. } assert ((y, x) ∈ T × S) as H7. { apply H1; auto. }
    apply In_prod_def in H7 as [_ H7]. auto.
Qed.

Lemma lemma_12_5 : forall (U : Type) (S T : Ensemble U),
  S = T <-> S − T = T − S.
Proof.
  intros U S T. split.
  - intros H1. apply set_equal_def. intros x. rewrite set_equal_def in H1. specialize (H1 x) as [H1 H2]. 
    split; intros H3; solve_in_Intersection_Union_helper_2.
  - intros H1. apply set_equal_def. intros x. rewrite set_equal_def in H1. specialize (H1 x) as [H1 H2].
    split; intros H3.
    -- pose proof classic (x ∈ T) as [H4 | H4]; auto. assert (x ∈ S − T) as H5. { solve_in_Intersection_Union_helper_2. }
       specialize (H1 H5). solve_in_Intersection_Union_helper_2.
    -- pose proof classic (x ∈ S) as [H4 | H4]; auto. assert (x ∈ T − S) as H5. { solve_in_Intersection_Union_helper_2. }
       specialize (H2 H5). solve_in_Intersection_Union_helper_2.
Qed.

Lemma lemma_12_6 : 
  (forall (U : Type) (S T : Ensemble U), S = T <-> S − T ⊆ T) -> False.
Proof.
  intros H1. specialize (H1 Z ⦃1⦄ ⦃1,2⦄). destruct H1 as [_ H1].
  replace (⦃1⦄ − ⦃1,2⦄) with (∅ : Ensemble Z) in H1.
  2 : { apply set_equal_def. intros x. split. intros H2. contradiction. intros H2. solve_in_Intersection_Union_helper_2. }
  assert (H2 : (∅ : Ensemble Z) ⊆ ⦃1,2⦄) by (intros x H2; contradiction). specialize (H1 H2).
  rewrite set_equal_def in H1. specialize (H1 2) as [_ H1]. assert (2 ∈ ⦃1,2⦄) as H3 by solve_in_Intersection_Union_helper_2.
  specialize (H1 H3). assert (H4 : 2 ∉ ⦃1⦄) by solve_not_in_ensemble. contradiction.
Qed.

Lemma lemma_12_7_a : forall (U : Type) (S : Ensemble U),
  (∅ : Ensemble U) × S = ∅.
Proof.
  intros U S. apply set_equal_def. intros x. split. intros H1.
  - inversion H1 as [y1 [y2 [H2 [H3 H4]]]]. contradiction.
  - contradiction.  
Qed.

Lemma lemma_12_7_b : forall (U : Type) (S : Ensemble U),
  S × (∅ : Ensemble U) = ∅.
Proof.
  intros U S. apply set_equal_def. intros x. split; intros H1.
  - inversion H1 as [y1 [y2 [H2 [H3 H4]]]]. contradiction.
  - contradiction.
Qed.

Lemma lemma_12_8 : forall (U : Type) (S T : Ensemble U),
  S × T = ∅ <-> S = ∅ \/ T = ∅.
Proof.
  intros U S T. split.
  - intros H1. rewrite set_equal_def in H1. pose proof (classic (S = ∅)) as [H2 | H2]; pose proof (classic (T = ∅)) as [H3 | H3]; auto.
    exfalso. apply not_Empty_In in H2 as [x H2]. apply not_Empty_In in H3 as [y H3]. specialize (H1 (x, y)) as [H1 _].
    assert ((x, y) ∈ ∅ -> False) as H5 by contradiction. apply H5. apply H1. exists x, y; auto.
  - intros [H1 | H1]; rewrite H1; [apply lemma_12_7_a | apply lemma_12_7_b].
Qed.

Lemma lemma_12_9_a : forall (U : Type) (A B C : Ensemble U),
  A × B ⊆ B × C -> B ≠ ∅ -> A ⊆ C.
Proof.
  intros U A B C H1 H2 x H3. assert (x ∈ B) as H5. { apply not_Empty_In in H2 as [y H2]. specialize (H1 (x, y)) as H5.
  assert ((x, y) ∈ A × B) as H6. { exists x, y; auto. } specialize (H5 H6). apply In_prod_def in H5 as [H5 _]. auto. }
  rewrite Subset_def in H1. specialize (H1 (x, x)) as H4. assert ((x, x) ∈ A × B) as H6. { exists x, x; auto. }
  specialize (H4 H6). apply In_prod_def in H4 as [_ H4]. auto.
Qed.

Lemma lemma_12_9_b : 
  (forall (U : Type) (A B C : Ensemble U), A × B ⊆ B × C -> A ⊆ C) -> False.
Proof.
  intros H1. specialize (H1 Z ⦃1,2⦄ ∅ ⦃1⦄). rewrite lemma_12_7_b, lemma_12_7_a in H1.
  assert (H2 : (∅ : Ensemble (Z * Z)) ⊆ ∅) by (apply Subset_refl). specialize (H1 H2).
  rewrite Subset_def in H1. specialize (H1 2). assert (2 ∈ ⦃1,2⦄) as H3 by solve_in_Intersection_Union_helper_2.
  specialize (H1 H3). assert (2 ∉ ⦃1⦄) as H4 by solve_not_in_ensemble. contradiction.
Qed.

Lemma lemma_12_10 : 
  (forall (U : Type) (A B C D : Ensemble U), A × B ⊆ C × D -> A ⊆ C /\ B ⊆ D) -> False.
Proof.
  intros H1. specialize (H1 Z ⦃1,2⦄ ∅ ⦃1⦄⦃1⦄). rewrite lemma_12_7_b in H1.
  assert (H2 : ∅ ⊆ ⦃1⦄ × ⦃1⦄ ) by apply Empty_Subset. specialize (H1 H2). destruct H1 as [H1 _].
  assert (⦃1,2⦄ ⊈ ⦃1⦄) as H3. { apply not_Subset_def. exists 2. split. solve_in_Intersection_Union_helper_2. solve_not_in_ensemble. }
  contradiction.
Qed.