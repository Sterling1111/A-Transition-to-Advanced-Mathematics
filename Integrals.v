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

Lemma Sorted_Rlt_nth : forall (l : list ℝ) (i1 i2 : ℕ),
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

Lemma Sorted_Rlt_NoDup : forall (l : list ℝ),
  Sorted Rlt l -> NoDup l.
Proof.
  intros l H1. apply (NoDup_nth l 0). intros i1 i2 H3 H4 H5. assert (i1 = i2 \/ i1 < i2 \/ i2 < i1)%nat as [H6 | [H6 | H6]]; try lia.
  - pose proof Sorted_Rlt_nth l i1 i2 H1 ltac:(lia) as H7. lra.
  - pose proof Sorted_Rlt_nth l i2 i1 H1 ltac:(lia) as H7. lra.
Qed.

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

Lemma nth_first_partition_R : forall (a b : ℝ) (p : partition_R a b),
  nth 0 p.(points a b) 0 = a.
Proof.
  intros a b [p]. simpl. pose proof Sorted_Rlt_NoDup p ltac:(auto) as H1.
  pose proof In_nth p a 0 ltac:(auto) as [n [H2 H3]]. pose proof Sorted_Rlt_nth p 0 n ltac:(auto) as H4.
  assert (n = 0 \/ n > 0)%nat as [H5 | H5]; try lia.
  - subst. auto.
  - specialize (H4 ltac:(lia)). pose proof nth_In as H6. specialize (H6 R 0%nat p 0 ltac:(lia)).
    specialize (partiton_R_P10 (nth 0 p 0) H6). lra. 
Qed.

Lemma nth_last_partition_R : forall (a b : ℝ) (p : partition_R a b),
  nth (length p.(points a b) - 1) p.(points a b) 0 = b.
Proof.
  intros a b [p]. simpl. pose proof Sorted_Rlt_NoDup p ltac:(auto) as H1.
  pose proof In_nth p b 0 ltac:(auto) as [n [H2 H3]]. pose proof Sorted_Rlt_nth p n (length p - 1) ltac:(auto) as H4.
  assert (n = length p - 1 \/ n < length p - 1)%nat as [H5 | H5]; try lia.
  - subst. auto.
  - specialize (H4 ltac:(lia)). pose proof nth_In as H6. specialize (H6 R (length p - 1)%nat p 0 ltac:(lia)).
    specialize (partiton_R_P10 (nth (length p - 1) p 0) H6). lra.
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

Lemma In_make_pairs : forall (l1 : list ℝ) (l2 : list (ℝ * ℝ)) (x : ℝ * ℝ),
  List.In x l2 -> l2 = make_pairs l1 -> List.In (fst x) l1 /\ List.In (snd x) l1.
Proof.
  intros l1 l2 x H1 H2. pose proof In_nth l2 x (0, 0) H1 as [i [H3 H4]].
  pose proof make_pairs_nth_elements l1 l2 i H2 H3 as H5. split.
  - rewrite <- H4, H5. simpl. apply nth_In. pose proof make_pairs_length l1 as H6. subst. lia.
  - rewrite <- H4, H5. simpl. apply nth_In. pose proof make_pairs_length l1 as H6. subst. lia.
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
  pose proof Sorted_Rlt_nth l1 i (i+1) ltac:(auto) ltac:(fold l2 in H3; lia) as H4.
  unfold p1. rewrite H2. simpl. apply H4.
Qed.

Lemma bounded_On_sub_intervals : forall (a b : ℝ) (p : partition_R a b) (f : ℝ -> ℝ),
  let l1 := p.(points a b) in
  let l2 := make_pairs l1 in
  bounded_On f a b -> Forall (fun p => bounded_On f (fst p) (snd p)) l2.
Proof.
  intros a b p f l1 l2 H1. apply Forall_forall. intros x H2.
  pose proof make_pairs_sorted a b p as H3. pose proof In_nth l2 x (0, 0) H2 as [i [H4 H5]].
  specialize (H3 i ltac:(auto)). unfold l2, l1 in H5. rewrite H5 in H3.
  pose proof bounded_On_sub_interval f a (fst x) b (snd x) ltac:(auto) as H6. apply H6.
  pose proof nth_first_partition_R a b p as H7. pose proof nth_last_partition_R a b p as H8.
  destruct p as [p]; simpl in *. apply In_make_pairs with (l1 := l1) in H2 as [H2 H2']; auto.
  specialize (partiton_R_P10 (fst x) H2) as H9. specialize (partiton_R_P10 (snd x) H2') as H10. lra.
Qed.

Lemma partion_sublist_elem_has_inf :  forall (f : ℝ -> ℝ) (a b : ℝ) (p : partition_R a b),
  let l1 := p.(points a b) in
  let l2 := make_pairs l1 in
  bounded_On f a b ->
  { l3 : list ℝ | forall (i : ℕ), (i < length l2)%nat -> is_glb (fun y => exists x, x ∈ [fst (nth i l2 (0, 0)), snd (nth i l2 (0, 0))] /\ y = f x) (nth i l3 0) }. 
Proof.
  intros f a b p l1 l2 H1. simpl in *. assert (Sorted Rlt l1) as H2 by (destruct p; auto).
  assert (H3 : forall x, List.In x l1 -> a <= x <= b). { intros x H3. destruct p; auto. }
   induction l1 as [| h t IH].
  - exists []. simpl. lia.
  - destruct IH as [l3 IH].
    -- apply Sorted_inv in H2. tauto.
    -- intros x H4. apply H3. right. auto.
    -- destruct t as [| h' t']. exists []. unfold l2. simpl. lia. unfold l2. rewrite make_pairs_cons.
       assert (h <= h') as H4. { apply Sorted_inv in H2 as [_ H2]. apply HdRel_inv in H2. lra. }
       assert (a <= h) as H5. { apply H3. left. auto. } assert (h' <= b) as H6. { apply H3. right. left. auto. }
       assert (bounded_On f h h') as H7. { apply bounded_On_sub_interval with (a := a) (b := b); auto. }
       pose proof interval_has_inf h h' f H7 as [inf H8]. exists (inf :: l3). intros i H9.
       assert (i = 0 \/ i > 0)%nat as [H10 | H10] by lia.
       * subst. unfold l2. simpl. auto.
       * specialize (IH (i-1)%nat). assert (i - 1 < length (make_pairs (h' :: t')))%nat as H11 by (simpl in *; lia).
         specialize (IH H11). replace (nth i ((h, h') :: make_pairs (h' :: t')) (0, 0)) with (nth (i-1) (make_pairs (h' :: t')) (0, 0)).
         2 : { destruct i. simpl; lia. replace (S i - 1)%nat with i by lia. reflexivity. }
         replace (nth i (inf :: l3) 0) with (nth (i-1) l3 0). 2 : { destruct i. simpl; lia. replace (S i - 1)%nat with i by lia. reflexivity. }
         auto.
Qed.

Lemma partion_sublist_elem_has_sup : forall (f : ℝ -> ℝ) (a b : ℝ) (p : partition_R a b),
  let l1 := p.(points a b) in
  let l2 := make_pairs l1 in
  bounded_On f a b ->
  { l3 : list ℝ | forall (i : ℕ), (i < length l2)%nat -> is_lub (fun y => exists x, x ∈ [fst (nth i l2 (0, 0)), snd (nth i l2 (0, 0))] /\ y = f x) (nth i l3 0) }.
Proof.
  intros f a b p l1 l2 H1. simpl in *. assert (Sorted Rlt l1) as H2 by (destruct p; auto).
  assert (H3 : forall x, List.In x l1 -> a <= x <= b). { intros x H3. destruct p; auto. }
   induction l1 as [| h t IH].
  - exists []. simpl. lia.
  - destruct IH as [l3 IH].
    -- apply Sorted_inv in H2. tauto.
    -- intros x H4. apply H3. right. auto.
    -- destruct t as [| h' t']. exists []. unfold l2. simpl. lia. unfold l2. rewrite make_pairs_cons.
       assert (h <= h') as H4. { apply Sorted_inv in H2 as [_ H2]. apply HdRel_inv in H2. lra. }
       assert (a <= h) as H5. { apply H3. left. auto. } assert (h' <= b) as H6. { apply H3. right. left. auto. }
       assert (bounded_On f h h') as H7. { apply bounded_On_sub_interval with (a := a) (b := b); auto. }
       pose proof interval_has_sup h h' f H7 as [sup H8]. exists (sup :: l3). intros i H9.
       assert (i = 0 \/ i > 0)%nat as [H10 | H10] by lia.
       * subst. unfold l2. simpl. auto.
       * specialize (IH (i-1)%nat). assert (i - 1 < length (make_pairs (h' :: t')))%nat as H11 by (simpl in *; lia).
         specialize (IH H11). replace (nth i ((h, h') :: make_pairs (h' :: t')) (0, 0)) with (nth (i-1) (make_pairs (h' :: t')) (0, 0)).
         2 : { destruct i. simpl; lia. replace (S i - 1)%nat with i by lia. reflexivity. }
         replace (nth i (sup :: l3) 0) with (nth (i-1) l3 0). 2 : { destruct i. simpl; lia. replace (S i - 1)%nat with i by lia. reflexivity. }
         auto.
Qed.

Lemma partition_has_sup : forall (f : ℝ -> ℝ) (a b : ℝ) (p : partition_R a b),
  let P : Ensemble ℝ := list_to_ensemble (map f (p.(points a b))) in
  { sup | is_lub P sup }.
Proof.
  intros f a b [l P1 P2 P3 P4 P5] P. assert (H1 : Finite_set P).
  { exists (map f l). unfold P. auto. }
  assert (H2 : P ≠ ∅).
  { apply not_Empty_In. exists (f a). unfold P. apply In_list_to_ensemble. apply in_map_iff. exists a; auto. }
  pose proof Finite_R_set_upper_bound P H2 H1. apply completeness_upper_bound; auto.
Qed.

Definition lower_sum (a b : ℝ) (bf : bounded_function_R a b) (p : partition_R a b) : ℝ :=
  let f := bf.(f a b) in
  let bounded := bf.(bounded_function_R_P1 a b) in
  let l1 := p.(points a b) in
  let l2 := make_pairs l1 in
  let l3 := proj1_sig (partion_sublist_elem_has_inf f a b p bounded) in
  let n : ℕ := length l2 in
  ∑ 0 (n-1) (fun i => (nth i l3 0) * (nth (i+1) l1 0 - nth (i) l1 0)).

Definition upper_sum (a b : ℝ) (bf : bounded_function_R a b) (p : partition_R a b) : ℝ :=
  let f := bf.(f a b) in
  let bounded := bf.(bounded_function_R_P1 a b) in
  let l1 := p.(points a b) in
  let l2 := make_pairs l1 in
  let l3 := proj1_sig (partion_sublist_elem_has_sup f a b p bounded) in
  let n : ℕ := length l2 in
  ∑ 0 (n-1) (fun i => (nth i l3 0) * (nth (i+1) l1 0 - nth (i) l1 0)).

Notation "L( f , P ( a , b ) )" := (lower_sum a b f P) (at level 0, f at level 0, P at level 0, a at level 0, b at level 0, format "L( f , P ( a , b ) )").
Notation "U( f , P ( a , b ) )" := (upper_sum a b f P) (at level 0, f at level 0, P at level 0, a at level 0, b at level 0, format "U( f , P ( a , b ) )").

Section lower_upper_sum_test.
  Let f : ℝ → ℝ := λ x, x.
  Let a : ℝ := 1.
  Let b : ℝ := 3.
  Let l1 : list ℝ := [1; 2; 3].
  Let l2 : list (ℝ * ℝ) := make_pairs l1.

  Example test_l2 : l2 = [(1, 2); (2, 3)].
  Proof. auto_list. Qed.

  Lemma a_lt_b : a < b.
  Proof. unfold a, b. lra. Qed.

  Lemma l1_sorted : Sorted Rlt l1.
  Proof. unfold l1. repeat first [ apply Sorted_cons | apply Sorted_nil | apply HdRel_nil | apply HdRel_cons | lra ]. Qed.

  Lemma a_In_l1 : List.In a l1.
  Proof. unfold l1. unfold a. left. reflexivity. Qed.

  Lemma b_In_l1 : List.In b l1.
  Proof. unfold l1. unfold b. right. right. left. reflexivity. Qed.

  Lemma x_In_l1 : forall x, List.In x l1 -> a <= x <= b.
  Proof. unfold l1, a, b. intros x H1. destruct H1 as [H1 | [H1 | [H1 | H1]]]; inversion H1; lra. Qed.

  Let P : partition_R a b := mkRpartition a b l1 a_lt_b l1_sorted a_In_l1 b_In_l1 x_In_l1.

  Print P.

  Lemma f_bounded_On : bounded_On f a b.
  Proof.
    unfold bounded_On, f, a, b. repeat split; try lra.
    - exists 1. intros y [x [H1 H2]]. subst. unfold In in *. lra.
    - exists 3. intros y [x [H1 H2]]. subst. unfold In in *. lra.
  Qed.

  Let bf : bounded_function_R a b := mkRbounded_function a b f f_bounded_On.

  Print bf.

  Lemma glb_f_1_2_is_1 : is_glb (fun y => exists x, x ∈ [1, 2] /\ y = f x) 1.
  Proof.
    unfold is_glb, f. split.
    - intros y H1. destruct H1 as [x [H1 H2]]. subst. unfold In in *. lra.
    - intros lb H1. apply H1. exists 1. unfold In. lra.
  Qed.

  Lemma glb_f_2_3_is_2 : is_glb (fun y => exists x, x ∈ [2, 3] /\ y = f x) 2.
  Proof.
    unfold is_glb, f. split.
    - intros y H1. destruct H1 as [x [H1 H2]]. subst. unfold In in *. lra.
    - intros lb H1. apply H1. exists 2. unfold In. lra.
  Qed.

  Lemma lub_f_1_2_is_2 : is_lub (fun y => exists x, x ∈ [1, 2] /\ y = f x) 2.
  Proof.
    unfold is_lub, f. split.
    - intros y H1. destruct H1 as [x [H1 H2]]. subst. unfold In in *. lra.
    - intros ub H1. apply H1. exists 2. unfold In. lra.
  Qed.

  Lemma lub_f_2_3_is_3 : is_lub (fun y => exists x, x ∈ [2, 3] /\ y = f x) 3.
  Proof.
    unfold is_lub, f. split.
    - intros y H1. destruct H1 as [x [H1 H2]]. subst. unfold In in *. lra.
    - intros ub H1. apply H1. exists 3. unfold In. lra.
  Qed.

  Example test_lower_sum : L(bf, P(a, b)) = 3.
  Proof.
    unfold lower_sum, proj1_sig. simpl. rewrite sum_f_i_Sn_f; try lia. rewrite sum_f_0_0; try lia. simpl. 
    destruct (partion_sublist_elem_has_inf f a b P f_bounded_On) as [l3 H1]. specialize (H1 0%nat) as H2.
    specialize (H1 1%nat) as H3. replace (points a b P) with l1 in H2, H3 by auto. simpl in H2, H3.
    specialize (H2 ltac:(lia)). specialize (H3 ltac:(lia)). assert (nth 0 l3 0 = 1) as H4.
    { apply glb_unique with (E := fun y => exists x, x ∈ [1, 2] /\ y = f x); auto. apply glb_f_1_2_is_1. }
    assert (nth 1 l3 0 = 2) as H5.
    { apply glb_unique with (E := fun y => exists x, x ∈ [2, 3] /\ y = f x); auto. apply glb_f_2_3_is_2. }
    rewrite H4, H5. lra.
  Qed.

  Example test_upper_sum : U(bf, P(a, b)) = 5.
  Proof.
    unfold upper_sum, proj1_sig. simpl. rewrite sum_f_i_Sn_f; try lia. rewrite sum_f_0_0; try lia. simpl. 
    destruct (partion_sublist_elem_has_sup f a b P f_bounded_On) as [l3 H1]. specialize (H1 0%nat) as H2.
    specialize (H1 1%nat) as H3. replace (points a b P) with l1 in H2, H3 by auto. simpl in H2, H3.
    specialize (H2 ltac:(lia)). specialize (H3 ltac:(lia)). assert (nth 0 l3 0 = 2) as H4.
    { apply lub_unique with (E := fun y => exists x, x ∈ [1, 2] /\ y = f x); auto. apply lub_f_1_2_is_2. }
    assert (nth 1 l3 0 = 3) as H5.
    { apply lub_unique with (E := fun y => exists x, x ∈ [2, 3] /\ y = f x); auto. apply lub_f_2_3_is_3. }
    rewrite H4, H5. lra.
  Qed.

End lower_upper_sum_test.

Theorem lower_sum_lt_upper_sum : forall (f : ℝ -> ℝ) (a b : ℝ) (P : partition_R a b) (H1 : bounded_On f a b),
  let bf : bounded_function_R a b := mkRbounded_function a b f H1 in
  L(bf, P(a, b)) <= U(bf, P(a, b)).
Proof.
  intros f' a b P H' [f H1]; clear f' H'. unfold lower_sum, upper_sum, proj1_sig; simpl.
  destruct (partion_sublist_elem_has_inf f a b P H1) as [l2 H2]. destruct (partion_sublist_elem_has_sup f a b P H1) as [l3 H3].
  destruct P as [l1]. simpl in *.
Admitted.