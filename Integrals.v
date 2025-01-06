Require Import Imports Notations Completeness Sets Functions Sums Reals_util.
Import SetNotations IntervalNotations.

Open Scope interval_scope.

Record partition_R (a b : ℝ) : Type := mkRpartition
{
  points : list ℝ; 
  partiton_R_P1 : a < b;
  partiton_R_P2 : Sorted Rlt points;
  partiton_R_P3 : List.In a points;
  partiton_R_P4 : List.In b points;
  partiton_R_P5 : forall x, List.In x points -> a <= x <= b
}.

Lemma In_list_2_length : forall (l : list ℝ) (a b : ℝ),
  List.In a l -> List.In b l -> (a <> b) -> (length l >= 2)%nat.
Proof.
  intros l a b H1 H2 H3. destruct l as [| h t].
  - inversion H1.
  - destruct H2 as [H2 | H2']; destruct H1 as [H1 | H1']; destruct t; simpl in *; try lia; try lra.
Qed.

Lemma length_partition_R : forall (a b : ℝ) (p : partition_R a b),
  (length p.(points a b) >= 2)%nat.
Proof.
  intros a b [p]. simpl. apply (In_list_2_length p a b); auto. lra.
Qed.

Definition bounded_On (f : ℝ -> ℝ) (a b : ℝ) :=
  a < b /\ has_lower_bound (fun y => exists x, x ∈ [a, b] /\ y = f x) /\
  has_upper_bound (fun y => exists x, x ∈ [a, b] /\ y = f x).

Record bounded_function_R (a b : ℝ) : Type := mkRbounded_function
{
  f : ℝ -> ℝ;
  bounded_function_R_P1 : bounded_On f a b
}.

Lemma bounded_On_sub_interval : forall (f : ℝ -> ℝ) (a b : ℝ),
  bounded_On f a b -> forall a' b', (a < a' < b') -> (b' < b) -> bounded_On f a' b'.
Proof.
  intros f a b [_ [[lb H1] [ub H2]]] a' b' [H3 H4] H5. split; auto. split.
  - exists lb. intros y [x [H6 H7]]. specialize (H1 y). apply H1. exists x. unfold In in *; split; lra.
  - exists ub. intros y [x [H6 H7]]. specialize (H2 y). apply H2. exists x. unfold In in *; split; lra.
Qed.

Lemma Finite_R_set_upper_bound : forall (A : Ensemble ℝ),
  A ≠ ∅ -> Finite_set A -> exists ub, is_upper_bound A ub.
Proof.
  intros A H1 H2. destruct H2 as [l H2]. generalize dependent A. induction l as [| h t IH].
  - intros A H1 H2. autoset.
  - intros A H1 H2. simpl in H2. pose proof classic (h ∈ list_to_ensemble t) as [H3 | H3].
    -- specialize (IH A H1). replace (⦃h⦄ ⋃ list_to_ensemble t) with (list_to_ensemble t) in H2.
       2 : { apply set_equal_def. intros x. split; intros H4; autoset. apply In_Union_def in H4 as [H4 | H4]; autoset.
             apply In_singleton_def in H4. subst. apply H3. }
       specialize (IH H2). auto.
    -- pose proof classic (list_to_ensemble t = ∅) as [H4 | H4].
       * exists h. intros x H5. replace A with (⦃h⦄) in H5. 2 : { rewrite H4 in H2. autoset. }
         apply In_singleton_def in H5. lra.
       * specialize (IH (list_to_ensemble t) H4 ltac:(auto)) as [ub H5]. exists (Rmax h ub).
         intros x H6. rewrite <- H2 in H6. apply In_Union_def in H6 as [H6 | H6].
         + apply In_singleton_def in H6. subst. solve_R.
         + specialize (H5 x H6). solve_R.
Qed.

Lemma Finite_R_set_lower_bound : forall (A : Ensemble ℝ),
  A ≠ ∅ -> Finite_set A -> exists lb, is_lower_bound A lb.
Proof.
  intros A H1 H2. destruct H2 as [l H2]. generalize dependent A. induction l as [| h t IH].
  - intros A H1 H2. autoset.
  - intros A H1 H2. simpl in H2. pose proof classic (h ∈ list_to_ensemble t) as [H3 | H3].
    -- specialize (IH A H1). replace (⦃h⦄ ⋃ list_to_ensemble t) with (list_to_ensemble t) in H2.
       2 : { apply set_equal_def. intros x. split; intros H4; autoset. apply In_Union_def in H4 as [H4 | H4]; autoset.
             apply In_singleton_def in H4. subst. apply H3. }
       specialize (IH H2). auto.
    -- pose proof classic (list_to_ensemble t = ∅) as [H4 | H4].
       * exists h. intros x H5. replace A with (⦃h⦄) in H5. 2 : { rewrite H4 in H2. autoset. }
         apply In_singleton_def in H5. lra.
       * specialize (IH (list_to_ensemble t) H4 ltac:(auto)) as [lb H5]. exists (Rmin h lb).
         intros x H6. rewrite <- H2 in H6. apply In_Union_def in H6 as [H6 | H6].
         + apply In_singleton_def in H6. subst. solve_R.
         + specialize (H5 x H6). solve_R.
Qed.

Lemma interval_has_inf : forall (a b : ℝ) (f : ℝ -> ℝ),
  bounded_On f a b ->
  { inf | is_glb (fun y => exists x, x ∈ [a, b] /\ y = f x) inf }.
Proof.
  intros a b f [H1 [H2 H3]]. set (A := fun y => exists x, x ∈ [a, b] /\ y = f x).
  assert (H4 : A ≠ ∅). { apply not_Empty_In. exists (f a). exists a; auto. split; auto. unfold In. lra. }
  apply completeness_lower_bound; auto. 
Qed. 

Lemma interval_has_sup : forall (a b : ℝ) (f : ℝ -> ℝ),
  bounded_On f a b ->
  { sup | is_lub (fun y => exists x, x ∈ [a, b] /\ y = f x) sup }.
Proof.
  intros a b f [H1 [H2 H3]]. set (A := fun y => exists x, x ∈ [a, b] /\ y = f x).
  assert (H4 : A ≠ ∅). { apply not_Empty_In. exists (f a). exists a; auto. split; auto. unfold In. lra. }
  apply completeness_upper_bound; auto.
Qed.

Lemma Sorted_Rlt_nth_implies_lt : forall (l : list ℝ),
  Sorted Rlt l -> 
  forall i1 i2, 
    (i1 < i2 < length l)%nat ->
    nth i1 l 0 < nth i2 l 0.
Proof.
  intros l H1 i1 i2 H2. generalize dependent i2. generalize dependent i1. induction l as [| h t IH].
  - intros i1 i2 H2. simpl in H2. lia.
  - intros i1 i2 H2. inversion H1. specialize (IH H3). assert (i1 = 0 \/ i1 > 0)%nat as [H5 | H5];
    assert (i2 = 0 \/ i2 > 0)%nat as [H6 | H6]; try lia.
    -- rewrite H5. replace (nth 0 (h :: t) 0) with h by auto. replace (nth i2 (h :: t) 0) with (nth (i2-1) t 0).
       2 : { destruct i2; simpl; try lia. rewrite Nat.sub_0_r. reflexivity. } assert (h < nth 0 t 0) as H7.
Admitted.

Fixpoint make_pairs (l : list ℝ) : list (ℝ * ℝ) :=
  match l with
  | [] => []
  | h :: t => match t with
         | [] => []
         | h' :: t' => (h, h') :: make_pairs t
       end
  end.

Example test_make_pairs : make_pairs [1; 2; 3; 4; 5] = [(1, 2); (2, 3); (3, 4); (4, 5)].
Proof.
  auto_list.
Qed.

Open Scope nat_scope.

Lemma make_pairs_cons : forall (l : list ℝ) (h1 h2 : ℝ),
  make_pairs (h1 :: h2 :: l) = (h1, h2) :: make_pairs (h2 :: l).
Proof.
  induction l. reflexivity.
  intros h1 h2. replace (make_pairs (h2 :: a :: l)) with ((h2, a) :: make_pairs (a :: l)) by auto_list.
  rewrite <- IHl. replace (make_pairs (h1 :: h2 :: a :: l)) with ((h1, h2) :: make_pairs (h2 :: a :: l)) by auto_list.
  reflexivity.
Qed.

Lemma make_pairs_length : forall (l : list ℝ),
  length (make_pairs l) = length l - 1.
Proof.
  intros l. induction l as [| h t IH].
  - simpl. lia.
  - destruct t as [| h' t'].
    -- simpl. lia.
    -- rewrite make_pairs_cons. replace (length ((h, h') :: make_pairs (h' :: t'))) with (S (length (make_pairs (h' :: t')))).
       2 : { simpl. lia. } rewrite IH. simpl. lia.
Qed.

Lemma grestt : forall (l : list (ℝ * ℝ)) (f : ℝ -> ℝ),
  Forall 
Proof.
Qed.

Lemma partition_list_of_infimums : forall (a b : ℝ) (p : partition_R a b),
  exists l : list ℝ, forall i, (i < length l)%nat -> nth i l 0 = proj1_sig ()
Proof.
  intros l. exists (map (fun i => (nth i l 0, nth (i+1) l 0)) (seq 0 (length l - 1))). split.
  - rewrite length_map. rewrite length_seq. auto.
  - intros i H1.
Admitted.

Lemma pairs_has : 
Proof.
Qed.

Lemma partition_has_sup_list : forall (f : ℝ -> ℝ) (a b : ℝ) (p : partition_R a b),
  let l := p.(points a b) in
  { l' : list ℝ | forall i, (i < length l)%nat -> nth i points 0 = f (nth i points 0) }.
Proof.
Qed.

Lemma partition_has_inf : forall (f : ℝ -> ℝ) (a b : ℝ) (p : Rpartition a b),
  let P : Ensemble ℝ := list_to_ensemble (map f (p.(l a b))) in
  { inf | is_glb P inf }.
Proof.
  intros f a b [l P1 P2 P3 P4 P5] P. assert (H1 : Finite_set P).
  { exists (map f l). unfold P. auto. }
  assert (H2 : P ≠ ∅).
  { apply not_Empty_In. exists (f a). unfold P. apply In_list_to_ensemble. apply in_map_iff. exists a; auto. }
  pose proof Finite_R_set_lower_bound P H2 H1. apply completeness_lower_bound; auto.
Qed.

Lemma partition_has_inf_list : forall (f : ℝ -> ℝ) (a b : ℝ) (p : Rpartition a b),
  let P : Ensemble ℝ := list_to_ensemble (map f (p.(l a b))) in
  { inf | is_glb P inf }.
Proof.
Qed.

Lemma partition_has_sup : forall (f : ℝ -> ℝ) (a b : ℝ) (p : Rpartition a b),
  let P : Ensemble ℝ := list_to_ensemble (map f (p.(l a b))) in
  { sup | is_lub P sup }.
Proof.
  intros f a b [l P1 P2 P3 P4 P5] P. assert (H1 : Finite_set P).
  { exists (map f l). unfold P. auto. }
  assert (H2 : P ≠ ∅).
  { apply not_Empty_In. exists (f a). unfold P. apply In_list_to_ensemble. apply in_map_iff. exists a; auto. }
  pose proof Finite_R_set_upper_bound P H2 H1. apply completeness_upper_bound; auto.
Qed.

Definition lower_sum (f : ℝ -> ℝ) (a b : ℝ) (p : Rpartition a b) : ℝ :=
  let l := p.(l a b) in
  let n : ℕ := length l in
  let P : Ensemble ℝ := list_to_ensemble (map f l) in
  let inf : ℝ := proj1_sig (partition_has_inf f a b p) in
  ∑ 1 (n-1) (fun i => inf * (nth i l 0 - nth (i-1) l 0)).

Definition upper_sum (f : ℝ -> ℝ) (a b : ℝ) (p : Rpartition a b) : ℝ :=
  let l := p.(l a b) in
  let n : ℕ := length l in
  let P : Ensemble ℝ := list_to_ensemble (map f l) in
  let sup : ℝ := proj1_sig (partition_has_sup f a b p) in
  ∑ 1 (n-1) (fun i => sup * (nth i l 0 - nth (i-1) l 0)).

Notation "L( f , P( a , b ) )" := (lower_sum f a b) (at level 0).
Notation "U( f , P( a , b ) )" := (upper_sum f a b) (at level 0).

