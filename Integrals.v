Require Import Imports Notations Completeness Sets Functions Sums Reals_util Continuity Derivatives Limit Pigeonhole.
Import SetNotations IntervalNotations.

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
  - exists lb. intros y [x [H4 H5]]. specialize (H1 y). apply H1. exists x. unfold Ensembles.In in *; split; lra.
  - exists ub. intros y [x [H4 H5]]. specialize (H2 y). apply H2. exists x. unfold Ensembles.In in *; split; lra.
Qed.

Lemma interval_has_inf : forall (a b : ℝ) (f : ℝ -> ℝ),
  bounded_On f a b ->
  { inf | is_glb (fun y => exists x, x ∈ [a, b] /\ y = f x) inf }.
Proof.
  intros a b f [H1 [H2 H3]]. set (A := fun y => exists x, x ∈ [a, b] /\ y = f x).
  assert (H4 : A ≠ ∅). { apply not_Empty_In. exists (f a). exists a; auto. split; auto. unfold Ensembles.In. lra. }
  apply completeness_lower_bound; auto. 
Qed. 

Lemma interval_has_sup : forall (a b : ℝ) (f : ℝ -> ℝ),
  bounded_On f a b ->
  { sup | is_lub (fun y => exists x, x ∈ [a, b] /\ y = f x) sup }.
Proof.
  intros a b f [H1 [H2 H3]]. set (A := fun y => exists x, x ∈ [a, b] /\ y = f x).
  assert (H4 : A ≠ ∅). { apply not_Empty_In. exists (f a). exists a; auto. split; auto. unfold Ensembles.In. lra. }
  apply completeness_upper_bound; auto.
Qed.

Lemma partition_sublist_elem_has_inf :  forall (f : ℝ -> ℝ) (a b : ℝ) (p : partition_R a b),
  let l1 := p.(points a b) in
  bounded_On f a b ->
  { l2 : list ℝ | (length l2 = length l1 - 1)%nat /\ forall (i : ℕ), (i < length l2)%nat -> is_glb (fun y => exists x, x ∈ [nth i l1 0, nth (i+1)%nat l1 0] /\ y = f x) (nth i l2 0) }. 
Proof.
  intros f a b p l1 H1. assert (Sorted Rlt l1) as H2 by (destruct p; auto).
  assert (H3 : forall x, List.In x l1 -> a <= x <= b). { intros x H3. destruct p; auto. }
  induction l1 as [| h t IH].
  - exists []; split; simpl; lia.
  - destruct IH as [l2 [IH1 IH2]].
    -- apply Sorted_inv in H2. tauto.
    -- intros x H4. apply H3. right. auto.
    -- destruct t as [| h' t']. exists []. split; simpl; lia. assert (h <= h') as H4. { apply Sorted_inv in H2 as [_ H2]. apply HdRel_inv in H2. lra. }
       assert (a <= h) as H5. { apply H3. left. auto. } assert (h' <= b) as H6. { apply H3. right. left. auto. }
       assert (bounded_On f h h') as H7. { apply bounded_On_sub_interval with (a := a) (b := b); auto. }
       pose proof interval_has_inf h h' f H7 as [inf H8]. exists (inf :: l2). split. simpl. rewrite IH1. simpl. lia. intros i H9.
       assert (i = 0 \/ i > 0)%nat as [H10 | H10] by lia.
       * subst. simpl. auto.
       * specialize (IH2 (i-1)%nat). assert (i - 1 < length l2)%nat as H11 by (simpl in *; lia).
         specialize (IH2 H11). replace (i-1+1)%nat with i in IH2 by lia.
         replace (nth i (h :: h' :: t') 0) with (nth (i-1)%nat (h' :: t') 0). 2 : { destruct i. simpl; lia. replace (S i - 1)%nat with i by lia. reflexivity. }
         replace (nth (i + 1) (h :: h' :: t') 0) with (nth i (h' :: t') 0). 2 : { destruct i. simpl; lia. replace (S i + 1)%nat with (S (S i)) by lia. reflexivity. }
         replace (nth i (inf :: l2) 0) with (nth (i-1)%nat l2 0). 2 : { destruct i. simpl; lia. replace (S i - 1)%nat with i by lia. reflexivity. } auto.
Qed.

Lemma partition_sublist_elem_has_sup : forall (f : ℝ -> ℝ) (a b : ℝ) (p : partition_R a b),
  let l1 := p.(points a b) in
  bounded_On f a b ->
  { l2 : list ℝ | (length l2 = length l1 - 1)%nat /\ forall (i : ℕ), (i < length l2)%nat -> is_lub (fun y => exists x, x ∈ [nth i l1 0, nth (i+1)%nat l1 0] /\ y = f x) (nth i l2 0) }.
Proof.
  intros f a b p l1 H1. assert (Sorted Rlt l1) as H2 by (destruct p; auto).
  assert (H3 : forall x, List.In x l1 -> a <= x <= b). { intros x H3. destruct p; auto. }
  induction l1 as [| h t IH].
  - exists []; split; simpl; lia.
  - destruct IH as [l2 [IH1 IH2]].
    -- apply Sorted_inv in H2. tauto.
    -- intros x H4. apply H3. right. auto.
    -- destruct t as [| h' t']. exists []. split; simpl; lia. assert (h <= h') as H4. { apply Sorted_inv in H2 as [_ H2]. apply HdRel_inv in H2. lra. }
       assert (a <= h) as H5. { apply H3. left. auto. } assert (h' <= b) as H6. { apply H3. right. left. auto. }
       assert (bounded_On f h h') as H7. { apply bounded_On_sub_interval with (a := a) (b := b); auto. }
       pose proof interval_has_sup h h' f H7 as [sup H8]. exists (sup :: l2). split. simpl. rewrite IH1. simpl. lia.
       intros i H9. assert (i = 0 \/ i > 0)%nat as [H10 | H10] by lia.
       * subst. simpl. auto.
       * specialize (IH2 (i-1)%nat). assert (i - 1 < length l2)%nat as H11 by (simpl in *; lia).
         specialize (IH2 H11). replace (i-1+1)%nat with i in IH2 by lia.
         replace (nth i (h :: h' :: t') 0) with (nth (i-1)%nat (h' :: t') 0). 2 : { destruct i. simpl; lia. replace (S i - 1)%nat with i by lia. reflexivity. }
         replace (nth (i + 1) (h :: h' :: t') 0) with (nth i (h' :: t') 0). 2 : { destruct i. simpl; lia. replace (S i + 1)%nat with (S (S i)) by lia. reflexivity. }
         replace (nth i (sup :: l2) 0) with (nth (i-1)%nat l2 0). 2 : { destruct i. simpl; lia. replace (S i - 1)%nat with i by lia. reflexivity. } auto.
Qed.

Definition lower_sum (a b : ℝ) (bf : bounded_function_R a b) (p : partition_R a b) : ℝ :=
  let f := bf.(f a b) in
  let bounded := bf.(bounded_function_R_P1 a b) in
  let l1 := p.(points a b) in
  let l2 := proj1_sig (partition_sublist_elem_has_inf f a b p bounded) in
  let n : ℕ := length l2 in
  let sum_term := fun i => (nth i l2 0) * (nth (i+1) l1 0 - nth (i) l1 0) in
  sum_f 0 (n-1) sum_term.

Definition upper_sum (a b : ℝ) (bf : bounded_function_R a b) (p : partition_R a b) : ℝ :=
  let f := bf.(f a b) in
  let bounded := bf.(bounded_function_R_P1 a b) in
  let l1 := p.(points a b) in
  let l2 := proj1_sig (partition_sublist_elem_has_sup f a b p bounded) in
  let n : ℕ := length l2 in
  sum_f 0 (n-1) (fun i => (nth i l2 0) * (nth (i+1) l1 0 - nth (i) l1 0)).

Notation "L( f , P ( a , b ) )" := (lower_sum a b f P) (at level 70, f, a, b, P at level 0).
Notation "U( f , P ( a , b ) )" := (upper_sum a b f P) (at level 70, f, a, b, P at level 0).

Section lower_upper_sum_test.
  Let f : ℝ → ℝ := λ x, x.
  Let a : ℝ := 1.
  Let b : ℝ := 3.
  Let l1 : list ℝ := [1; 2; 3].

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
    - exists 1. intros y [x [H1 H2]]. subst. unfold Ensembles.In in *. lra.
    - exists 3. intros y [x [H1 H2]]. subst. unfold Ensembles.In in *. lra.
  Qed.

  Let bf : bounded_function_R a b := mkRbounded_function a b f f_bounded_On.

  Print bf.

  Lemma glb_f_1_2_is_1 : is_glb (fun y => exists x, x ∈ [1, 2] /\ y = f x) 1.
  Proof.
    unfold is_glb, f. split.
    - intros y H1. destruct H1 as [x [H1 H2]]. subst. unfold Ensembles.In in *. lra.
    - intros lb H1. apply H1. exists 1. unfold Ensembles.In. lra.
  Qed.

  Lemma glb_f_2_3_is_2 : is_glb (fun y => exists x, x ∈ [2, 3] /\ y = f x) 2.
  Proof.
    unfold is_glb, f. split.
    - intros y H1. destruct H1 as [x [H1 H2]]. subst. unfold Ensembles.In in *. lra.
    - intros lb H1. apply H1. exists 2. unfold Ensembles.In. lra.
  Qed.

  Lemma lub_f_1_2_is_2 : is_lub (fun y => exists x, x ∈ [1, 2] /\ y = f x) 2.
  Proof.
    unfold is_lub, f. split.
    - intros y H1. destruct H1 as [x [H1 H2]]. subst. unfold Ensembles.In in *. lra.
    - intros ub H1. apply H1. exists 2. unfold Ensembles.In. lra.
  Qed.

  Lemma lub_f_2_3_is_3 : is_lub (fun y => exists x, x ∈ [2, 3] /\ y = f x) 3.
  Proof.
    unfold is_lub, f. split.
    - intros y H1. destruct H1 as [x [H1 H2]]. subst. unfold Ensembles.In in *. lra.
    - intros ub H1. apply H1. exists 3. unfold Ensembles.In. lra.
  Qed.

  Let l2_lower : list ℝ := proj1_sig (partition_sublist_elem_has_inf f a b P f_bounded_On).
  Let l2_upper : list ℝ := proj1_sig (partition_sublist_elem_has_sup f a b P f_bounded_On).

  Lemma l2_lower_eq : l2_lower = [1; 2].
  Proof.
    unfold l2_lower, proj1_sig in *. destruct (partition_sublist_elem_has_inf f a b P f_bounded_On) as [l2 [H1 H2]].
    specialize (H2 0%nat) as H3. specialize (H2 1%nat) as H4. replace (points a b P) with l1 in H1, H3, H4 by auto.
    simpl in H3, H4. specialize (H3 ltac:(simpl in *; lia)). specialize (H4 ltac:(simpl in *; lia)).
    assert (nth 0 l2 0 = 1) as H5.
    { apply glb_unique with (E := fun y => exists x, x ∈ [1, 2] /\ y = f x); auto. apply glb_f_1_2_is_1. }
    assert (nth 1 l2 0 = 2) as H6.
    { apply glb_unique with (E := fun y => exists x, x ∈ [2, 3] /\ y = f x); auto. apply glb_f_2_3_is_2. }
    destruct l2 as [| h1 [| h2 t]]; simpl in H1; try lia. simpl in H5. simpl in H6.
    assert (t = []). { apply length_zero_iff_nil; lia. } subst. auto.
  Qed.

  Lemma l2_upper_eq : l2_upper = [2; 3].
  Proof.
    unfold l2_upper, proj1_sig in *. destruct (partition_sublist_elem_has_sup f a b P f_bounded_On) as [l2 [H1 H2]].
    specialize (H2 0%nat) as H3. specialize (H2 1%nat) as H4. replace (points a b P) with l1 in H1, H3, H4 by auto.
    simpl in H3, H4. specialize (H3 ltac:(simpl in *; lia)). specialize (H4 ltac:(simpl in *; lia)).
    assert (nth 0 l2 0 = 2) as H5.
    { apply lub_unique with (E := fun y => exists x, x ∈ [1, 2] /\ y = f x); auto. apply lub_f_1_2_is_2. }
    assert (nth 1 l2 0 = 3) as H6.
    { apply lub_unique with (E := fun y => exists x, x ∈ [2, 3] /\ y = f x); auto. apply lub_f_2_3_is_3. }
    destruct l2 as [| h1 [| h2 t]]; simpl in H1; try lia. simpl in H5. simpl in H6.
    assert (t = []). { apply length_zero_iff_nil; lia. } subst. auto.
  Qed.

  Example test_lower_sum : L(bf, P(a, b)) = 3.
  Proof. 
    unfold lower_sum, proj1_sig in *. simpl. pose proof l2_lower_eq as H1. unfold l2_lower in H1.
    destruct (partition_sublist_elem_has_inf f a b P f_bounded_On) as [l2 [H2 H3]]. subst.
    simpl. sum_simpl. lra.
  Qed.

  Example test_upper_sum : U(bf, P(a, b)) = 5.
  Proof.
    unfold upper_sum, proj1_sig in *. simpl. pose proof l2_upper_eq. unfold l2_upper in H.
    destruct (partition_sublist_elem_has_sup f a b P f_bounded_On) as [l2 [H1 H2]]. subst.
    simpl. sum_simpl. lra.
  Qed.

End lower_upper_sum_test.

Theorem lower_sum_le_upper_sum : forall (a b : ℝ) (bf : bounded_function_R a b) (P : partition_R a b),
  L(bf, P(a, b)) <= U(bf, P(a, b)).
Proof.
  intros a b [f H1] P. unfold lower_sum, upper_sum, proj1_sig; simpl.
  destruct (partition_sublist_elem_has_inf f a b P H1) as [l2 [H2 H3]]. destruct (partition_sublist_elem_has_sup f a b P H1) as [l3 [H4 H5]].
  destruct P as [l1]; simpl in *. assert (H6 : forall i, (i < length l1 - 1)%nat -> nth i l2 0 <= nth i l3 0).
  {
    intros i H6. specialize (H3 i ltac:(lia)). specialize (H5 i ltac:(lia)).
    destruct H3 as [H3 _], H5 as [H5 _]. unfold is_lower_bound in H3. specialize (H3 (f (nth i l1 0))). specialize (H5 (f(nth i l1 0))).
    pose proof Sorted_Rlt_nth l1 i (i+1) ltac:(auto) ltac:(lia) as H7.
    assert (f (nth i l1 0) ∈ (λ y : ℝ, ∃ x : ℝ, x ∈ (λ x0 : ℝ, nth i l1 0 <= x0 <= nth (i + 1) l1 0) ∧ y = f x)) as H8.
    { exists (nth i l1 0). split. unfold Ensembles.In. lra. auto. }
    specialize (H3 H8). specialize (H5 H8). lra. 
  }
  replace (length l3) with (length l2) by lia. apply sum_f_congruence_le; try lia. intros k H7.
  assert (length l2 = 0 \/ length l2 > 0)%nat as [H8 | H8] by lia.
  - rewrite length_zero_iff_nil in H8. rewrite H8 in H2. simpl in H2. rewrite <- H2 in H4.
    apply length_zero_iff_nil in H4. subst. replace k with 0%nat. 2 : { simpl in H7. lia. } lra.
  - specialize (H6 k ltac:(lia)). assert (forall i, (i < length l1 - 1)%nat -> nth i l1 0 < nth (i+1) l1 0) as H9.
    { intros i H9. apply Sorted_Rlt_nth; auto; lia. } specialize (H9 k ltac:(lia)). nra.
Qed.

Lemma incl_NoDup_len : forall (l1 l2 : list ℝ),
  NoDup l1 -> NoDup l2 -> List.incl l1 l2 -> (length l1 <= length l2)%nat.
Proof.
  intros l1 l2 H1 H2 H3. assert (length l1 < length l2 \/ length l1 = length l2 \/ length l1 > length l2)%nat as [H4 | [H4 | H4]]; try lia.
  pose proof pigeonhole_principle_list ℝ l1 l2. apply H in H3; auto. tauto.
Qed.

Fixpoint insert_Sorted_Rlt (r : ℝ) (l : list ℝ) : list ℝ := 
match l with
  | [] => [r]
  | h :: t => if Rlt_dec r h then r :: l else h :: insert_Sorted_Rlt r t
end.

Lemma insert_Sorted_Rlt_in : forall (r : ℝ) (l : list ℝ),
  List.In r (insert_Sorted_Rlt r l).
Proof.
  intros r l. induction l as [| h t IH].
  - simpl; auto.
  - simpl. destruct (Rlt_dec r h) as [H1 | H1].
    -- left; auto.
    -- right. apply IH.
Qed.

Lemma insert_Sorted_Rlt_first : forall (r : ℝ) (l : list ℝ),
  Sorted Rlt l -> nth 0 (insert_Sorted_Rlt r l) 0 = r \/ nth 0 (insert_Sorted_Rlt r l) 0 = nth 0 l 0.
Proof.
  intros r l H1. destruct l as [| h t].
  - simpl; auto.
  - simpl. apply Sorted_inv in H1 as [H1 _]. destruct (Rlt_dec r h) as [H2 | H2].
    -- left. auto.
    -- right. simpl. auto.
Qed.

Lemma insert_Sorted_Rlt_sorted : forall (r : ℝ) (l : list ℝ),
  NoDup l -> Sorted Rlt l -> ~List.In r l -> Sorted Rlt (insert_Sorted_Rlt r l).
Proof.
  intros r l H1 H2 H3. induction l as [| h t IH].
  - simpl; auto.
  - apply NoDup_cons_iff in H1 as [_ H1]. apply Sorted_inv in H2 as [H2 H4].
    assert (~List.In r t) as H5. { intros H5. apply H3. right. auto. } specialize (IH H1 H2 H5). simpl.
    destruct (Rlt_dec r h) as [H6 | H6]. 
    -- repeat constructor; auto.
    -- repeat constructor; auto. assert (H7 : r <> h). { intros H7. apply H3. left; auto. }
       assert (H8 : h < r) by lra. pose proof insert_Sorted_Rlt_first r t H2 as [H9 | H9].
       + destruct (insert_Sorted_Rlt r t). constructor. apply HdRel_cons. simpl in H9; lra.
       + destruct t. simpl. apply HdRel_cons. lra. apply HdRel_inv in H4.
         destruct (insert_Sorted_Rlt r (r0 :: t)). apply HdRel_nil. apply HdRel_cons. simpl in H9. lra.
Qed.  

Lemma lemma_13_1_a : forall (a b : ℝ) (bf : bounded_function_R a b) (Q P : partition_R a b),
  List.incl (P.(points a b)) (Q.(points a b)) -> L(bf, P(a, b)) <= L(bf, Q(a, b)).
Proof.
  intros a b [f H1] Q P H2. unfold lower_sum, proj1_sig; simpl.
  destruct (partition_sublist_elem_has_inf f a b P H1) as [l3 [H3 H4]];
  destruct (partition_sublist_elem_has_inf f a b Q H1) as [l4 [H5 H6]];
  destruct P as [l1]; destruct Q as [l2]; simpl in *. 
Admitted.

Definition Integrable_On (f : ℝ -> ℝ) (a b : ℝ) :=
  exists (bf : bounded_function_R a b) (sup inf : ℝ), bf.(Integrals.f a b) = f /\
    let LS := (fun x : ℝ => exists p : partition_R a b, x = L(bf, p(a, b))) in
    let US := (fun x : ℝ => exists p : partition_R a b, x = U(bf, p(a, b))) in
    is_lub LS sup /\ is_glb US inf /\ sup = inf.

Definition integral (f : ℝ -> ℝ) (a b r : ℝ) : Prop :=  
  exists (bf : bounded_function_R a b), bf.(Integrals.f a b) = f /\
    let LS := (fun x : ℝ => exists p : partition_R a b, x = L(bf, p(a, b))) in
    let US := (fun x : ℝ => exists p : partition_R a b, x = U(bf, p(a, b))) in
    is_lub LS r /\ is_glb US r.

Definition integral_minus (f1 f2 : ℝ -> ℝ) (a b c d r : ℝ) : Prop :=
  exists r1 r2, integral f1 a b r1 /\ integral f2 c d r2 /\ r = r1 - r2.

Notation "∫ a b f '=' r" := 
 (integral f a b r)
   (at level 70, f, a, b, r at level 0, no associativity, format "∫  a  b  f  '='  r").

Notation "∫ a b f1 - ∫ c d f2 = r" :=
  (integral_minus f1 f2 a b c d r)
    (at level 70, f1, f2, a, b, c, d, r at level 0, no associativity, format "∫  a  b  f1  -  ∫  c  d  f2  =  r").

Theorem FTC1 : forall f F a b,
  (forall x, x ∈ [a, b] -> ∫ a x f = (F x)) -> continuous_on f [a, b] -> ⟦ der ⟧ F ⦅a, b⦆ = f.
Proof.
  intros f F a b H1 H2 c H3. unfold derivative_at.
  assert (H4 : forall h, h ∈ ⦅0, (b - c)⦆ -> ∫ a (c + h) f - ∫ a c f = (F (c + h) - F c)).
  { 
    intros h H4. specialize (H1 (c + h) ltac:(unfold Ensembles.In in *; lra)) as H5. 
    specialize (H1 c ltac:(unfold Ensembles.In in *; lra)) as H6. exists (F (c + h)), (F c). split; auto.
  }
  specialize (H1 c H3) as H4.
Qed.