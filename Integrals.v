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
  a <= b /\ has_lower_bound (fun y => exists x, x ∈ [a, b] /\ y = f x) /\
  has_upper_bound (fun y => exists x, x ∈ [a, b] /\ y = f x).

Record bounded_function_R (a b : ℝ) : Type := mkRbounded_function
{
  f : ℝ -> ℝ;
  bounded_function_R_P1 : bounded_On f a b
}.

Lemma bounded_On_sub_interval : forall (f : ℝ -> ℝ) (a a' b b' : ℝ),
  bounded_On f a b -> (a <= a' <= b' <= b) -> bounded_On f a' b'.
Proof.
  intros f a b a' b' [_ [[lb H1] [ub H2]]] H3. repeat split; try lra.
  - exists lb. intros y [x [H4 H5]]. specialize (H1 y). apply H1. exists x. unfold In in *; split; lra.
  - exists ub. intros y [x [H4 H5]]. specialize (H2 y). apply H2. exists x. unfold In in *; split; lra.
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

Lemma Sorted_Rlt_nth_implies_lt : forall (l : list ℝ) (i1 i2 : ℕ),
  Sorted Rlt l -> (i1 < i2 < length l)%nat -> nth i1 l 0 < nth i2 l 0.
Proof.
  intros l i1 i2 H1 H2. generalize dependent i2. generalize dependent i1. induction l as [| h t IH].
  - intros i1 i2 H2. simpl in H2. lia.
  - intros i1 i2 H2. inversion H1. specialize (IH H3). assert (i1 = 0 \/ i1 > 0)%nat as [H5 | H5];
    assert (i2 = 0 \/ i2 > 0)%nat as [H6 | H6]; try lia.
    -- rewrite H5. replace (nth 0 (h :: t) 0) with h by auto. replace (nth i2 (h :: t) 0) with (nth (i2-1) t 0).
       2 : { destruct i2; simpl; try lia. rewrite Nat.sub_0_r. reflexivity. } destruct t as [| h' t'].
       * simpl in H2. lia.
       * assert (h < h') as H7. { apply HdRel_inv in H4. auto. } simpl in H2. assert (i2-1 = 0 \/ i2-1 > 0)%nat as [H8 | H8]; try lia.
         { rewrite H8. simpl. auto. } specialize (IH 0%nat (i2-1)%nat ltac:(simpl; lia)). replace (nth 0 (h' :: t') 0) with h' in IH by auto. lra.
    -- replace (nth i1 (h :: t) 0) with (nth (i1-1) t 0). 2 : { destruct i1; simpl; try lia. rewrite Nat.sub_0_r. reflexivity. }
       replace (nth i2 (h :: t) 0) with (nth (i2-1) t 0). 2 : { destruct i2; simpl; try lia. rewrite Nat.sub_0_r. reflexivity. }
       destruct t as [| h' t'].
       * simpl in H2. lia.
       * assert (h < h') as H7. { apply HdRel_inv in H4. auto. } assert (i1-1 = 0 \/ i1-1 > 0)%nat as [H8 | H8];
         assert (i2-1 = 0 \/ i2-1 > 0)%nat as [H9 | H9]; try lia.
         + rewrite H8. specialize (IH 0%nat (i2-1)%nat ltac:(simpl in *; lia)). auto.
         + specialize (IH (i1-1)%nat (i2 -1)%nat ltac:(simpl in *; lia)). auto.
Qed.

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

Close Scope nat_scope.

Lemma make_pairs_nth_elements : forall (l1 : list ℝ) (l2 : list (ℝ * ℝ)) (i : ℕ),
  l2 = make_pairs l1 -> (i < length l2)%nat -> nth i l2 (0, 0) = (nth i l1 0, nth (i+1) l1 0).
Proof.
  intros l1 l2 i H1 H2. generalize dependent l2. generalize dependent i. induction l1 as [| h t IH].
  - intros i l2 H1 H2. simpl in H1. rewrite H1 in H2. simpl in H2. lia.
  - intros i l2 H1 H2. destruct l2 as [| h' t']; try (simpl in H2; lia).
    destruct t as [| h'' t''].
    -- simpl in H1. inversion H1.
    -- rewrite make_pairs_cons in H1. injection H1 as H3 H4. rewrite H3. assert (i = 0 \/ i > 0)%nat as [H5 | H5] by lia.
       + rewrite H5. simpl. reflexivity.
       + replace (nth i ((h, h'') :: t') (0, 0)) with 
         (nth (i-1)%nat t' (0, 0)). 2 : { destruct i. lia. simpl. rewrite Nat.sub_0_r. reflexivity. }
         replace (nth i (h :: h'' :: t'') 0) with (nth (i-1)%nat (h'' :: t'') 0). 
         2 : { destruct i. lia. replace (S i - 1)%nat with i by lia. reflexivity. }
         replace (nth (i + 1) (h :: h'' :: t'') 0) with (nth i (h'' :: t'') 0). 
         2 : { destruct i. lia. replace (S i + 1)%nat with (S (S i)) by lia. reflexivity. }
         specialize (IH (i-1)%nat t'). replace (i-1+1)%nat with i in IH by lia. apply IH.
         2 : { simpl in H2. lia. } rewrite H4. destruct t''. simpl. reflexivity. rewrite make_pairs_cons. reflexivity.
Qed.  

Lemma make_pairs_sorted : forall (a b : ℝ) (p : partition_R a b) (i : ℕ),
  let l1 := p.(points a b) in
  let l2 := make_pairs l1 in
  let p1 := nth i l2 (0, 0) in
  (i < length l2)%nat -> fst p1 < snd p1.
Proof.
  intros a b [p] i l1 l2 p1 H1; simpl in *. 
  pose proof make_pairs_nth_elements l1 l2 i ltac:(auto) H1 as H2.
  pose proof make_pairs_length l1 as H3.
  pose proof Sorted_Rlt_nth_implies_lt l1 i (i+1) ltac:(auto) ltac:(fold l2 in H3; lia) as H4.
  unfold p1. rewrite H2. simpl. apply H4.
Qed.

Lemma gtrest : forall (a b : ℝ) (p : partition_R a b) (f : ℝ -> ℝ),
  let l1 := p.(points a b) in
  let l2 := make_pairs l1 in
  bounded_On f a b -> Forall (fun p => bounded_On f (fst p) (snd p)) l2.
Proof.
  intros a b p f l1 l2 H1. apply Forall_forall. intros x H2.
  pose proof make_pairs_sorted a b p as H3. pose proof In_nth l2 x (0, 0) H2 as [i [H4 H5]].
  specialize (H3 i ltac:(auto)). unfold l2, l1 in H5. rewrite H5 in H3.
  pose proof bounded_On_sub_interval f a (fst x) b (snd x) ltac:(auto) as H6. apply H6.
  destruct p as [p]; simpl in *. pose proof Sorted_Rlt_nth_implies_lt p. p i (i+1) p.(partiton_R_P2) ltac:(auto) ltac:(auto).
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

