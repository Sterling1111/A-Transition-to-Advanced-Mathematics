Require Import Imports Notations Completeness Sets Functions Sums Reals_util Continuity Derivatives Limit Pigeonhole.
Import SetNotations IntervalNotations.

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
  intros l H1. induction l as [| h t IH].
  - constructor.
  - apply Sorted_inv in H1 as [H1 H2]. constructor; auto. intros H3. specialize (IH H1).
    pose proof In_nth t h 0 H3 as [n [H4 H5]].
    pose proof Sorted_Rlt_nth t as H6. destruct t as [| h' t'].
    -- inversion H3.
    -- specialize (H6 0%nat n H1). assert (n = 0 \/ n > 0)%nat as [H7 | H7] by lia.
       * subst. simpl in H2. apply HdRel_inv in H2. lra.
       * specialize (H6 ltac:(lia)). rewrite H5 in H6. simpl in H6. apply HdRel_inv in H2. lra.
Qed.

Lemma Sorted_Rlt_eq : forall l1 l2,
  Sorted Rlt l1 -> Sorted Rlt l2 -> (forall x, List.In x l1 <-> List.In x l2) -> l1 = l2.
Proof.
  intros l1 l2 H1 H2 H3. generalize dependent l2. induction l1 as [| h t IH].
  - intros l2 H2 H3. destruct l2 as [| h t]; auto. specialize (H3 h). destruct H3 as [_ H3]. specialize (H3 ltac:(left; auto)). inversion H3.
  - intros l2 H2 H3. destruct l2 as [| h2 t2].
    * specialize (H3 h) as [H3 _]. specialize (H3 ltac:(left; auto)). inversion H3.
    * pose proof Sorted_Rlt_NoDup (h :: t) H1 as H4. pose proof (Sorted_Rlt_NoDup (h2 :: t2) H2) as H5.
      specialize (IH ltac:(apply Sorted_inv in H1; tauto) t2 ltac:(apply Sorted_inv in H2; tauto)).
      assert (h = h2) as H6.
      {
        pose proof Rtotal_order h h2 as [H6 | [H6 | H6]]; auto.
        - assert (h2 < h) as H7.
          {
            specialize (H3 h) as [H3 _]. specialize (H3 ltac:(left; auto)).
            pose proof In_nth (h2 :: t2) h 0 H3 as [n [H7 H8]]. 
            assert (n = 0 \/ n > 0)%nat as [H9 | H9] by lia; subst. simpl in H6. lra.
            pose proof Sorted_Rlt_nth (h2 :: t2) 0 n H2 ltac:(lia) as H10. 
            replace (nth 0 (h2 :: t2) 0) with h2 in H10 by reflexivity. lra.
          } lra.
        - assert (h < h2) as H7.
          {
            specialize (H3 h2) as [_ H3]. specialize (H3 ltac:(left; auto)).
            pose proof In_nth (h :: t) h2 0 H3 as [n [H7 H8]]. 
            assert (n = 0 \/ n > 0)%nat as [H9 | H9] by lia; subst. simpl in H6. lra.
            pose proof Sorted_Rlt_nth (h :: t) 0 n H1 ltac:(lia) as H10. 
            replace (nth 0 (h :: t) 0) with h in H10 by reflexivity. lra.
          } lra.
      }
      f_equal; auto. apply IH. intros x; split; intros H7.
      + assert (x <> h) as H8. { intros H8. subst. apply NoDup_cons_iff in H4 as [H8 _]. apply H8. apply H7. }
        specialize (H3 x) as [H3 _]. specialize (H3 ltac:(right; auto)). destruct H3 as [H3 | H3]; auto. lra.
      + assert (x <> h2) as H8. { intros H8. subst. apply NoDup_cons_iff in H5 as [H8 _]. apply H8. apply H7. }
        specialize (H3 x) as [_ H3]. specialize (H3 ltac:(right; auto)). destruct H3 as [H3 | H3]; auto. lra.
Qed.

Record partition_R (a b : ℝ) : Type := mkRpartition
{
  points : list ℝ; 
  partition_R_P1 : a < b;
  partition_R_P2 : Sorted Rlt points;
  partition_R_P3 : List.In a points;
  partition_R_P4 : List.In b points;
  partition_R_P5 : forall x, List.In x points -> a <= x <= b
}.

Lemma partition_length : forall a b (P : partition_R a b),
  (length (P.(points a b)) >= 2)%nat.
Proof.
  intros a b P. destruct P as [l1 H1 H2 H3 H4 H5]. simpl.
  destruct l1 as [| h t]. inversion H3. destruct t as [| h' t'].
  - simpl in *; lra.
  - simpl; lia.
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

Notation "L( f , P ( a , b ) )" := (lower_sum a b f P) (at level 70, f, a, b, P at level 0, format "L( f ,  P ( a ,  b ) )").
Notation "U( f , P ( a , b ) )" := (upper_sum a b f P) (at level 70, f, a, b, P at level 0, format "U( f ,  P ( a ,  b ) )").

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

Lemma insert_Sorted_Rlt_length : forall (r : ℝ) (l : list ℝ),
  length (insert_Sorted_Rlt r l) = S (length l).
Proof.
  intros r l. induction l as [| h t IH].
  - simpl; auto.
  - simpl. destruct (Rlt_dec r h) as [H1 | H1].
    -- simpl. lia.
    -- simpl. lia.
Qed.

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
  Sorted Rlt l -> ~List.In r l -> Sorted Rlt (insert_Sorted_Rlt r l).
Proof.
  intros r l H2 H3. pose proof Sorted_Rlt_NoDup l H2 as H1. induction l as [| h t IH].
  - simpl; auto.
  - apply NoDup_cons_iff in H1 as [_ H1]. apply Sorted_inv in H2 as [H2 H4].
    assert (~List.In r t) as H5. { intros H5. apply H3. right. auto. } specialize (IH H2 H5). simpl.
    destruct (Rlt_dec r h) as [H6 | H6]. 
    -- repeat constructor; auto.
    -- repeat constructor; auto. assert (H7 : r <> h). { intros H7. apply H3. left; auto. }
       assert (H8 : h < r) by lra. pose proof insert_Sorted_Rlt_first r t H2 as [H9 | H9].
       + destruct (insert_Sorted_Rlt r t). constructor. apply HdRel_cons. simpl in H9; lra.
       + destruct t. simpl. apply HdRel_cons. lra. apply HdRel_inv in H4.
         destruct (insert_Sorted_Rlt r (r0 :: t)). apply HdRel_nil. apply HdRel_cons. simpl in H9. lra.
Qed.

Lemma In_l_In_insert_Sorted_Rlt : forall (l : list ℝ) (r a : ℝ),
  List.In a l -> List.In a (insert_Sorted_Rlt r l).
Proof.
  intros l r a H1. induction l as [| h t IH].
  - simpl; auto.
  - simpl. destruct (Rlt_dec r h) as [H2 | H2].
    -- destruct H1 as [H1 | H1]; subst. right; left; auto. right; right; auto.
    -- destruct H1 as [H1 | H1]; subst. left; auto. right; auto.
Qed.

Lemma firstn_nth_eq : forall (l1 l2 : list ℝ) (n i : ℕ),
  firstn n l1 = firstn n l2 -> (i < n)%nat -> nth i l1 0 = nth i l2 0.
Proof.
  induction l1 as [| h t IH]; intros l2 n i H1 H2.
  - rewrite firstn_nil in H1. assert (length (firstn n l2) = 0)%nat as H3. { rewrite <- H1. simpl. reflexivity. }
    rewrite length_firstn in H3. assert (n = 0 \/ length l2 = 0)%nat as [H4 | H4]; try lia. rewrite length_zero_iff_nil in H4. subst. reflexivity.
  - destruct l2 as [| h' t']; destruct n as [| n']; destruct i as [| i']; try lia; try inversion H1; auto.
    simpl. specialize (IH t' n' i'). apply IH. inversion H1. auto. lia.
Qed.

Lemma skipn_eq_nil : forall (l : list ℝ) (n : ℕ),
  skipn n l = [] -> (length l <= n)%nat.
Proof.
  induction l as [| h t IH]; intros n H1.
  - destruct n. simpl. lia. simpl. lia.
  - destruct n as [| n']; try lia. simpl in H1. rewrite H1. simpl. lia. simpl in *. specialize (IH n' H1). lia.
Qed.

Lemma skipn_nth_eq : forall (l1 l2 : list ℝ) (n i : ℕ),
  skipn n l1 = skipn n l2 -> (i >= n)%nat -> nth i l1 0 = nth i l2 0.
Proof.
  induction l1 as [| h t IH]; intros l2 n i H1 H2.
  - rewrite skipn_nil in H1. assert (length (skipn n l2) = 0)%nat as H3. { rewrite <- H1. simpl. reflexivity. }
    rewrite length_skipn in H3. rewrite nth_overflow with (l := l2); try lia. destruct i; simpl; reflexivity.
  - destruct l2 as [| h' t']; destruct n as [| n']; destruct i as [| i']; try lia; try inversion H1; auto. 
    rewrite H0. simpl. apply skipn_eq_nil in H0. apply nth_overflow. lia. 
    simpl. specialize (IH t' n' i'). rewrite IH; auto. lia. 
Qed.

Lemma skipn_nth_eq' : forall (l1 l2 : list ℝ) (n i : ℕ),
  skipn n l1 = skipn (n+1) l2 -> (i >= n)%nat -> nth i l1 0 = nth (i+1) l2 0.
Proof.
  induction l1 as [| h t IH]; intros l2 n i H1 H2.
  - rewrite skipn_nil in H1. assert (length (skipn (n+1) l2) = 0)%nat as H3. { rewrite <- H1. simpl. reflexivity. }
    rewrite length_skipn in H3. rewrite nth_overflow with (l := l2); try lia. destruct i; simpl; reflexivity.
  - destruct l2 as [| h' t']; destruct n as [| n']; destruct i as [| i']; try lia; try inversion H1; auto.
    -- rewrite H0. simpl. apply skipn_eq_nil in H0. apply nth_overflow. lia.
    -- simpl in *. rewrite <- H. simpl. auto.
    -- simpl in *. rewrite <- H. specialize (IH t' 0%nat i'). subst. rewrite IH; auto. lia.
    -- simpl. specialize (IH t' n' i'). rewrite IH; auto. lia.
Qed.

Lemma insert_Sorted_Rlt_nth : forall (l1 l2 : list ℝ) (r : ℝ),
  Sorted Rlt l1 -> ~List.In r l1 -> l2 = insert_Sorted_Rlt r l1 -> 
    exists (i : ℕ), (i < length l2)%nat /\ nth i l2 0 = r /\ 
      (forall j, (j < i)%nat -> nth j l2 0 = nth j l1 0) /\ 
        (forall k, (i <= k)%nat -> nth (k+1) l2 0 = nth k l1 0).
Proof.
  intros l1 l2 r H1 H2 H3. pose proof insert_Sorted_Rlt_in r l1 as H4. pose proof In_nth l2 r 0 ltac:(subst; auto) as [n [H5 H6]].
  exists n; do 2 (split; auto). split; [intro j | intro k]; intro H7.
  - assert (firstn n l1 = firstn n l2) as H8.
    { apply Sorted_Rlt_eq. admit. admit. admit. } apply firstn_nth_eq with (n := n) (i := j) in H8; auto.
  - assert (skipn n l1 = skipn (n+1) l2) as H8.
    { apply Sorted_Rlt_eq. admit. admit. admit. } apply skipn_nth_eq' with (n := n) (i := k) in H8; auto.
Admitted.

Lemma partition_spec : forall (a b : ℝ) (P : partition_R a b),
  Sorted Rlt (P.(points a b)) /\ a < b /\ List.In a (P.(points a b)) /\ List.In b (P.(points a b)) /\
    (forall x, List.In x (P.(points a b)) -> a <= x <= b) /\ (length (P.(points a b)) >= 2)%nat /\ NoDup (P.(points a b)) /\
      nth 0 (P.(points a b)) 0 = a /\ nth (length (P.(points a b)) - 1) (P.(points a b)) 0 = b.
Proof.
  intros a b [l1 H1 H2 H3 H4 H5]; simpl. repeat (split; auto).
  - destruct l1 as [| h t]. inversion H3. destruct t as [| h' t']; simpl in *; try lra; try lia.
  - apply Sorted_Rlt_NoDup; auto.
  - destruct l1 as [| h t]. inversion H3. pose proof In_nth (h :: t) a 0 H3 as [n [H6 H7]]. assert (n = 0 \/ n > 0)%nat as [H8 | H8] by lia.
    -- subst. reflexivity.
    -- pose proof Sorted_Rlt_nth (h :: t) 0 n H2 ltac:(simpl in *; lia) as H9. rewrite H7 in H9. simpl in H9.
       specialize (H5 h). simpl in H5. lra.
  - pose proof In_nth l1 b 0 H4 as [n [H6 H7]]. assert (n = (length l1 - 1) \/ n < length l1 - 1)%nat as [H8 | H8] by lia.
    -- subst. reflexivity.
    -- pose proof Sorted_Rlt_nth l1 n (length l1 - 1) H2 ltac:(lia) as H9. specialize (H5 (nth (length l1 - 1) l1 0)).
       assert (List.In (nth (length l1 - 1) l1 0) l1) as H10. { apply nth_In. lia. } specialize (H5 H10). rewrite H7 in H9. lra.
Qed.

Lemma insert_Parition_R_not_first_or_last : forall (a b r : ℝ) (P Q : partition_R a b) (i : ℕ),
  let l1 := P.(points a b) in
  let l2 := Q.(points a b) in
  ~List.In r l1 -> l2 = insert_Sorted_Rlt r l1 -> nth i l2 0 = r -> (i > 0 /\ i < length l2 - 1)%nat.
Proof.
  intros a b r P Q i l1 l2 H1 H2 H3. pose proof partition_spec a b P as H4. pose proof partition_spec a b Q as H5. split.
  -
Admitted.

Lemma glb_subset : forall (E1 E2 : Ensemble ℝ) r1 r2,
  is_glb E1 r1 -> is_glb E2 r2 -> E1 ⊆ E2 -> r2 <= r1.
Proof.
  intros E1 E2 r1 r2 H1 H2 H3. unfold is_glb in H1, H2. destruct H1 as [H1 H4], H2 as [H2 H5].
  specialize (H4 r2). apply Rge_le. apply H4. intros x H6. specialize (H3 x H6). specialize (H2 x). apply H2. auto.
Qed.

Lemma insert_Parition_R_lower_sum : forall (a b r : ℝ) (bf : bounded_function_R a b) (P Q : partition_R a b),
  let l1 := P.(points a b) in
  let l2 := Q.(points a b) in
  ~List.In r l1 -> l2 = insert_Sorted_Rlt r l1 -> L(bf, P(a, b)) <= L(bf, Q(a, b)).
Proof.
  intros a b r [f H1] P Q. unfold lower_sum, proj1_sig; simpl.
  destruct (partition_sublist_elem_has_inf f a b P H1) as [l3 [H2 H3]];
  destruct (partition_sublist_elem_has_inf f a b Q H1) as [l4 [H4 H5]]. pose proof partition_length a b P as H6.
  set (l1 := points a b P). set (l2 := points a b Q). replace (points a b P) with l1 in *; replace (points a b Q) with l2 in *; auto.
  intros H7 H8. pose proof insert_Sorted_Rlt_nth l1 l2 r ltac:(pose proof partition_spec a b P as H9; apply H9) H7 H8 as [i [H10 [H11 [H12 H13]]]].
  pose proof insert_Parition_R_not_first_or_last a b r P Q i H7 ltac:(auto) H11 as H14.
  assert (H15 : length l2 = S (length l1)). { rewrite H8. apply insert_Sorted_Rlt_length. } replace (points a b Q) with l2 in * by auto.
  assert (i = 1%nat \/ i > 1)%nat as [H16 | H16] by lia.
  - assert (length l3 = 1 \/ length l3 > 1)%nat as [H17 | H17] by lia.
    -- rewrite H17. replace (length l4 - 1)%nat with 1%nat by lia. repeat sum_simpl. assert (nth 0 l3 0 <= nth 0 l4 0) as H18.
       {
         specialize (H3 0%nat ltac:(lia)). specialize (H5 0%nat ltac:(lia)).
         apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth 0 l2 0, nth 1 l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth 0 l1 0, nth 1 l1 0] /\ y = f x)); auto. 
         intros x H18. rewrite H12 in H18; try lia. rewrite <- H13 with (k := 1%nat); try lia. destruct H18 as [x2 [H18 H19]]. exists x2. split; auto. unfold In in *.
         assert (Sorted Rlt l2). { rewrite H8. apply insert_Sorted_Rlt_sorted; auto. unfold l1. pose proof partition_spec a b P; tauto. }
         pose proof Sorted_Rlt_nth l2 1 2 ltac:(auto) ltac:(lia). simpl. lra.
       }
       assert (nth 0 l3 0 <= nth 1 l4 0) as H19.
       {
         specialize (H3 0%nat ltac:(lia)). specialize (H5 1%nat ltac:(simpl in *; lia)).
         apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth 1 l2 0, nth 2 l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth 0 l1 0, nth 1 l1 0] /\ y = f x)); auto.
         intros x [x2 [H19 H20]]. exists x2. split; auto. unfold In in *. replace 2%nat with (1 + 1)%nat in H19 by lia. rewrite H13 in H19; try lia. rewrite <- H12; try lia.
         assert (Sorted Rlt l2). { rewrite H8. apply insert_Sorted_Rlt_sorted; auto. unfold l1. pose proof partition_spec a b P; tauto. }
         pose proof Sorted_Rlt_nth l2 0 1 ltac:(auto) ltac:(lia). simpl. lra.
       }
       assert (nth 0 l1 0 < nth 1 l2 0) as H20.
       {
          assert (Sorted Rlt l1) as H20. { pose proof partition_spec a b P; tauto. } assert (Sorted Rlt l2) as H21. { pose proof partition_spec a b Q; tauto. }
          pose proof Sorted_Rlt_nth l1 0 1 ltac:(auto) ltac:(lia) as H22. pose proof Sorted_Rlt_nth l2 0 1 ltac:(auto) ltac:(lia) as H23. rewrite H12 in H23; try lia. lra.
       }
       replace (nth 2 l2 0) with (nth 1 l1 0). 2 : { replace 2%nat with (1 + 1)%nat by lia. rewrite H13; try lia. reflexivity. }
       replace (nth 0 l2 0) with (nth 0 l1 0). 2 : { rewrite H12; try lia. reflexivity. } assert (H21 : nth 0 l1 0 < nth 1 l1 0).
       { assert (Sorted Rlt l1) as H21. { pose proof partition_spec a b P; tauto. } pose proof Sorted_Rlt_nth l1 0 1 ltac:(auto) ltac:(lia) as H22. lra. }
       assert (nth 1 l2 0 < nth 1 l1 0) as H22.
       {
          assert (Sorted Rlt l1) as H22. { pose proof partition_spec a b P; tauto. } assert (Sorted Rlt l2) as H23. { pose proof partition_spec a b Q; tauto. }
          pose proof Sorted_Rlt_nth l2 1 (1+1) ltac:(auto) ltac:(lia) as H24. rewrite H13 in H24; try lia. lra.
       } nra.
    --  rewrite sum_f_Si with (n := (length l4 - 1)%nat); try lia. rewrite sum_f_Si with (n := (length l4 - 1)%nat); try lia.
        rewrite H16 in H11. simpl. rewrite sum_f_Si; try lia. simpl. 
        assert (∑ 1 (length l3 - 1) (λ i0 : ℕ, nth i0 l3 0 * (nth (i0 + 1) l1 0 - nth i0 l1 0)) <= ∑ 2 (length l4 - 1) (λ i0 : ℕ, nth i0 l4 0 * (nth (i0 + 1) l2 0 - nth i0 l2 0))) as H18.
        {
          rewrite sum_f_reindex' with (s := 1%nat). simpl. replace (length l3 - 1 + 1)%nat with (length l4 - 1)%nat by lia.
          apply sum_f_congruence_le; try lia. intros k H18. replace (k - 1 + 1)%nat with k by lia. 
          assert (nth (k-1) l3 0 <= nth k l4 0) as H19.
          {
            specialize (H3 (k-1)%nat ltac:(lia)). specialize (H5 k ltac:(lia)). replace (k-1+1)%nat with k in H3 by lia.
            apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth k l2 0, nth (k+1) l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth (k-1) l1 0, nth k l1 0] /\ y = f x)); auto.
            intros x [x2 [H19 H20]]. exists x2. split; auto. unfold In in *. rewrite H13 in H19; try lia.
            assert (Sorted Rlt l2) as H21. { pose proof partition_spec a b Q; tauto. } rewrite <- H13; try lia. replace (k - 1 + 1)%nat with k by lia. lra.
          }
          rewrite H13; try lia. replace (nth k l2 0) with (nth (k-1) l1 0). 2 : { replace k with (k - 1 + 1)%nat at 2 by lia. rewrite H13; try lia. reflexivity. }
          assert (Sorted Rlt l1) as H20. { pose proof partition_spec a b P; tauto. } pose proof Sorted_Rlt_nth l1 (k-1) k ltac:(auto) ltac:(lia) as H21. nra.
        } 
        assert (nth 0 l3 0 * (nth 1 l1 0 - nth 0 l1 0) <= nth 1 l4 0 * (nth 2 l2 0 - nth 1 l2 0) + nth 0 l4 0 * (nth 1 l2 0 - nth 0 l2 0)) as H19.
        {
          assert (nth 0 l1 0 < nth 1 l2 0 < nth 1 l1 0) as H19.
          {
            assert (Sorted Rlt l1) as H19. { pose proof partition_spec a b P; tauto. } assert (Sorted Rlt l2) as H20. { pose proof partition_spec a b Q; tauto. }
            pose proof Sorted_Rlt_nth l1 0 1 ltac:(auto) ltac:(lia) as H21. pose proof Sorted_Rlt_nth l1 1 2 ltac:(auto) ltac:(lia) as H22.
            pose proof Sorted_Rlt_nth l2 0 1 ltac:(auto) ltac:(lia) as H23. pose proof Sorted_Rlt_nth l2 1 2 ltac:(auto) ltac:(lia) as H24.
            rewrite H12 in H23; try lia. replace 2%nat with (1+1)%nat in H24 by lia. rewrite H13 in H24; try lia. lra.
          }
          assert (nth 0 l3 0 <= nth 1 l4 0) as H20.
          {
            specialize (H3 0%nat ltac:(lia)). specialize (H5 1%nat ltac:(lia)).
            apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth 1 l2 0, nth 2 l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth 0 l1 0, nth 1 l1 0] /\ y = f x)); auto.
            intros x [x2 [H20 H21]]. exists x2. split; auto. unfold In in *.  rewrite <- H13 with (k := 1%nat); try lia. simpl. lra.
          }
          assert (nth 0 l3 0 <= nth 0 l4 0) as H21.
          {
            specialize (H3 0%nat ltac:(lia)). specialize (H5 0%nat ltac:(lia)).
            apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth 0 l2 0, nth 1 l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth 0 l1 0, nth 1 l1 0] /\ y = f x)); auto.
            intros x [x2 [H21 H22]]. exists x2. split; auto. unfold In in *. rewrite <- H12; try lia. lra.
          }
          replace (nth 0 l2 0) with (nth 0 l1 0). 2 : { rewrite H12; try lia. reflexivity. } replace (nth 2 l2 0) with (nth 1 l1 0). 2 : { rewrite <- H13; try lia. reflexivity. } nra.
        } nra.
  - rewrite sum_f_split with (i := 0%nat) (j := (i-2)%nat) (n := (length l4 - 1)%nat); try lia. replace (S (i - 2)) with (i-1)%nat by lia.
    rewrite sum_f_Si with (i := (i-1)%nat); try lia. assert (S (i-1) = length l4 - 1 \/ S (i-1) < length l4 - 1)%nat as [H17 | H17] by lia.
    -- rewrite <- H17. rewrite sum_f_n_n. replace (S (i-1)) with i by lia. replace (i-1+1)%nat with i by lia. replace (length l3 - 1)%nat with (S (i-2))%nat by lia.
       rewrite sum_f_i_Sn_f; try lia. replace (S (i-2)) with (i-1)%nat by lia. 
       assert (∑ 0 (i - 2) (λ i0 : ℕ, nth i0 l3 0 * (nth (i0 + 1) l1 0 - nth i0 l1 0)) <= ∑ 0 (i - 2) (λ i0 : ℕ, nth i0 l4 0 * (nth (i0 + 1) l2 0 - nth i0 l2 0))) as H18.
       {
        apply sum_f_congruence_le; try lia. intros k H18. rewrite H12; try lia. rewrite H12; try lia. specialize (H3 k ltac:(lia)). specialize (H5 k ltac:(lia)).
        assert (nth k l3 0 <= nth k l4 0) as H19.
        {
          apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth k l2 0, nth (k + 1) l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth k l1 0, nth (k + 1) l1 0] /\ y = f x)); auto.
          intros x [x2 [H19 H20]]. exists x2. split; auto. unfold In in *. rewrite H12 in H19; try lia. rewrite H12 in H19; try lia. lra.
        } 
        assert (Sorted Rlt l1) as H20. { pose proof partition_spec a b P; tauto. } pose proof Sorted_Rlt_nth l1 k (k+1) ltac:(auto) ltac:(lia) as H21. nra.
       }
       replace (i-1+1)%nat with i by lia.
       assert (nth (i - 1) l3 0 * (nth i l1 0 - nth (i - 1) l1 0) <= (nth i l4 0 * (nth (i + 1) l2 0 - nth i l2 0) + nth (i - 1) l4 0 * (nth i l2 0 - nth (i - 1) l2 0))) as H19.
       {
         assert (nth (i - 1) l3 0 <= nth i l4 0) as H19.
         {
            specialize (H3 (i-1)%nat ltac:(lia)). specialize (H5 i ltac:(lia)). replace (i-1+1)%nat with i in H3 by lia.
            apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth i l2 0, nth (i+1) l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth (i-1) l1 0, nth i l1 0] /\ y = f x)); auto.
            intros x [x2 [H19 H20]]. exists x2. split; auto. unfold In in *. rewrite <- H12; try lia. rewrite <- H13; try lia. 
            assert (Sorted Rlt l2) as H21. { pose proof partition_spec a b Q; tauto. } pose proof Sorted_Rlt_nth l2 (i-1) i ltac:(auto) ltac:(lia) as H22. lra.
         }
         assert (nth (i-1) l3 0 <= nth (i-1) l4 0) as H20.
         {
          specialize (H3 (i-1)%nat ltac:(lia)). specialize (H5 (i-1)%nat ltac:(lia)). replace (i-1+1)%nat with i in H3, H5 by lia.
          apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth (i-1) l2 0, nth i l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth (i-1) l1 0, nth i l1 0] /\ y = f x)); auto.
          intros x [x2 [H20 H21]]. exists x2. split; auto. unfold In in *. rewrite <- H12; try lia. rewrite <- H13; try lia. 
          assert (Sorted Rlt l2) as H22. { pose proof partition_spec a b Q; tauto. } pose proof Sorted_Rlt_nth l2 i (i+1) ltac:(auto) ltac:(lia) as H23. lra.
         }
         assert (nth (i-1) l1 0 < nth i l2 0 < nth i l1 0) as H21.
         {
           assert (Sorted Rlt l2) as H22. { pose proof partition_spec a b Q; tauto. } pose proof Sorted_Rlt_nth l2 i (i+1) ltac:(auto) ltac:(lia) as H24.
           pose proof Sorted_Rlt_nth l2 (i-1) i ltac:(auto) ltac:(lia) as H25. rewrite H13 in H24; try lia. rewrite <- H12; try lia. lra.
         }
         replace (nth (i - 1) l2 0) with (nth (i-1) l1 0). 2 : { rewrite <- H12; try lia. reflexivity. } rewrite H13; try lia. nra.
       } nra.
    -- rewrite sum_f_split with (i := 0%nat)(j := (i-2)%nat) (n := (length l3 - 1)%nat); try lia.
       rewrite sum_f_Si with (i := S (i-2)); try lia. replace (S (S (i-2))) with i by lia.
       replace (S (i-2)) with (i-1)%nat by lia. replace (i-1+1)%nat with i by lia.
       rewrite sum_f_Si with (i := (S (i-1))); try lia. replace (S (S (i-1))) with (i+1)%nat by lia.
       rewrite sum_f_reindex with (s := 1%nat) (i := (i + 1)%nat); try lia. replace (i+1-1)%nat with i by lia.
       replace (length l4 - 1 - 1)%nat with (length l3 - 1)%nat by lia.
       replace (S (i-1)) with i by lia.
       assert (nth (i - 1) l3 0 * (nth i l1 0 - nth (i - 1) l1 0) <= nth i l4 0 * (nth (i + 1) l2 0 - nth i l2 0) + nth (i - 1) l4 0 * (nth i l2 0 - nth (i - 1) l2 0)) as H18.
       {
          assert (nth (i - 1) l3 0 <= nth i l4 0) as H18.
          {
            specialize (H3 (i-1)%nat ltac:(lia)). specialize (H5 i ltac:(lia)). replace (i-1+1)%nat with i in H3 by lia.
            apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth i l2 0, nth (i+1) l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth (i-1) l1 0, nth i l1 0] /\ y = f x)); auto.
            intros x [x2 [H18 H19]]. exists x2. split; auto. unfold In in *. rewrite <- H12; try lia. rewrite <- H13; try lia.
            assert (Sorted Rlt l2) as H20. { pose proof partition_spec a b Q; tauto. } pose proof Sorted_Rlt_nth l2 (i-1) i ltac:(auto) ltac:(lia) as H21. lra.
          }
          assert (nth (i-1) l3 0 <= nth (i-1) l4 0) as H19.
          {
            specialize (H3 (i-1)%nat ltac:(lia)). specialize (H5 (i-1)%nat ltac:(lia)). replace (i-1+1)%nat with i in H3, H5 by lia.
            apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth (i-1) l2 0, nth i l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth (i-1) l1 0, nth i l1 0] /\ y = f x)); auto.
            intros x [x2 [H19 H20]]. exists x2. split; auto. unfold In in *. rewrite <- H12; try lia. rewrite <- H13; try lia.
            assert (Sorted Rlt l2) as H21. { pose proof partition_spec a b Q; tauto. } pose proof Sorted_Rlt_nth l2 i (i+1) ltac:(auto) ltac:(lia) as H22. lra.
          }
          assert (nth (i-1) l1 0 < nth i l2 0 < nth i l1 0) as H21.
          {
            assert (Sorted Rlt l2) as H22. { pose proof partition_spec a b Q; tauto. } pose proof Sorted_Rlt_nth l2 i (i+1) ltac:(auto) ltac:(lia) as H24.
            pose proof Sorted_Rlt_nth l2 (i-1) i ltac:(auto) ltac:(lia) as H25. rewrite H13 in H24; try lia. rewrite <- H12; try lia. lra.
          }
          replace (nth (i - 1) l2 0) with (nth (i-1) l1 0). 2 : { rewrite <- H12; try lia. reflexivity. } rewrite H13; try lia. nra.
       }
       assert (∑ 0 (i - 2) (λ i0 : ℕ, nth i0 l3 0 * (nth (i0 + 1) l1 0 - nth i0 l1 0)) <= ∑ 0 (i - 2) (λ i0 : ℕ, nth i0 l4 0 * (nth (i0 + 1) l2 0 - nth i0 l2 0))) as H19.
       {
          apply sum_f_congruence_le; try lia. intros k H19. rewrite H12; try lia. rewrite H12; try lia. specialize (H3 k ltac:(lia)). specialize (H5 k ltac:(lia)).
          assert (nth k l3 0 <= nth k l4 0) as H20.
          {
            apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth k l2 0, nth (k + 1) l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth k l1 0, nth (k + 1) l1 0] /\ y = f x)); auto.
            intros x [x2 [H20 H21]]. exists x2. split; auto. unfold In in *. rewrite H12 in H20; try lia. rewrite H12 in H20; try lia. lra.
          }
          assert (Sorted Rlt l1) as H21. { pose proof partition_spec a b P; tauto. } pose proof Sorted_Rlt_nth l1 k (k+1) ltac:(auto) ltac:(lia) as H22. nra.
       }
       assert (∑ i (length l3 - 1) (λ i0 : ℕ, nth i0 l3 0 * (nth (i0 + 1) l1 0 - nth i0 l1 0)) <= (∑ i (length l3 - 1) (λ x : ℕ, nth (x + 1) l4 0 * (nth (x + 1 + 1) l2 0 - nth (x + 1) l2 0)))) as H20.
       {
          apply sum_f_congruence_le; try lia. intros k H20. replace (k + 1 + 1)%nat with (k + 2)%nat by lia.
          assert (nth k l3 0 <= nth (k+1) l4 0) as H21.
          {
            specialize (H3 k ltac:(lia)). specialize (H5 (k+1)%nat ltac:(lia)). replace (k + 1 + 1)%nat with (k + 2)%nat in H5 by lia.
            apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth (k+1) l2 0, nth (k+2) l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth k l1 0, nth (k+1) l1 0] /\ y = f x)); auto.
            intros x [x2 [H21 H22]]. exists x2. split; auto. unfold In in *. rewrite <- H13; try lia. replace (k + 2)%nat with (k + 1 + 1)%nat in H21 by lia.
            rewrite (H13 (k + 1)%nat) in H21; try lia. lra.
          }
          rewrite H13; try lia. replace (k + 2)%nat with (k + 1 + 1)%nat by lia. rewrite H13; try lia.
          assert (Sorted Rlt l1) as H22. { pose proof partition_spec a b P; tauto. } pose proof Sorted_Rlt_nth l1 k (k+1) ltac:(auto) ltac:(lia) as H23. nra.
       }
       lra.
Qed.

Lemma insert_Parition_R_upper_sum : forall (a b r : ℝ) (bf : bounded_function_R a b) (P Q : partition_R a b),
  let l1 := P.(points a b) in
  let l2 := Q.(points a b) in
  ~List.In r l1 -> l2 = insert_Sorted_Rlt r l1 -> U(bf, P(a, b)) >= U(bf, Q(a, b)).
Proof.
Admitted.

Fixpoint add_points_Sorted_Rlt (l1 diff : list ℝ) : list R := 
  match diff with
  | [] => l1
  | h :: t => add_points_Sorted_Rlt (insert_Sorted_Rlt h l1) t
  end.

Fixpoint find (l : list ℝ) (r : ℝ) : bool := 
  match l with 
  | [] => false
  | h :: t => if (Req_dec h r) then true else find t r
  end.

Fixpoint get_all_points (l1 l2 : list ℝ) : list ℝ := 
  match l2 with
  | [] => []
  | h :: t => if (find l1 h) then get_all_points l1 t else h :: get_all_points l1 t
  end.
  
Lemma partition_R_eq : forall (a b : ℝ) (P Q : partition_R a b),
  P = Q <-> P.(points a b) = Q.(points a b).
Proof.
  intros a b P Q. split; intros H1; subst; auto.
  destruct P as [l1]; destruct Q as [l2]; simpl in *. subst; f_equal; apply proof_irrelevance.
Qed.

Lemma exists_list_of_missing_elems : forall (a b : ℝ) (P Q : partition_R a b),
  let l1 := P.(points a b) in
  let l2 := Q.(points a b) in
  List.incl l1 l2 -> exists (l : list ℝ), add_points_Sorted_Rlt l1 l = l2 /\
    forall r, List.In r l -> ~List.In r l1.
Proof.
  intros a b P Q l1 l2 H1. exists (get_all_points l2 l1).
Admitted.

Lemma lemma_13_1_a : forall (a b : ℝ) (bf : bounded_function_R a b) (Q P : partition_R a b),
  List.incl (P.(points a b)) (Q.(points a b)) -> L(bf, P(a, b)) <= L(bf, Q(a, b)).
Proof.
  intros a b f Q P H2. destruct (exists_list_of_missing_elems a b P Q) as [l [H3 H3']]; auto.
  generalize dependent P.
  induction l as [| h t IH].
  - intros P H2 H3 H3'. simpl in H3. apply partition_R_eq in H3. subst. reflexivity.
  - intros P H2 H3 H3'. simpl in H3. assert (H4 : a < b). { pose proof partition_spec a b P; tauto. }
    set (l := insert_Sorted_Rlt h (points a b P)). assert (H5 : a < b). { pose proof partition_spec a b P; tauto. }
    assert (H6 : Sorted Rlt l). { unfold l. apply insert_Sorted_Rlt_sorted; auto. pose proof partition_spec a b P; tauto. apply H3'. left. auto. }
    assert (H7 : List.In a l). { admit. }
    assert (H8 : List.In b l). { admit. }
    assert (H9 : forall x, List.In x l -> a <= x <= b). { admit. }
    set (P' := mkRpartition a b l H5 H6 H7 H8 H9). specialize (IH P').
    assert (H10 : incl (points a b P') (points a b Q)). { admit. }
    assert (H11 : add_points_Sorted_Rlt (points a b P') t = points a b Q). { admit. }
    assert (H12 : (∀ r : ℝ, List.In r t → ¬ List.In r (points a b P'))). { intros r H12. admit. }
    specialize (IH H10 H11 H12). assert (L(f, P(a, b)) <= L(f, P'(a, b))). { apply insert_Parition_R_lower_sum with (r := h). apply H3'. left. auto. auto. }
    lra. 
Admitted.

Lemma lemma_13_1_b : forall (a b : ℝ) (bf : bounded_function_R a b) (Q P : partition_R a b),
  List.incl (P.(points a b)) (Q.(points a b)) -> U(bf, P(a, b)) >= U(bf, Q(a, b)).
Proof.
Admitted.

Lemma exists_partition_R_includes_both : forall (a b : ℝ) (P Q : partition_R a b),
  let l1 := P.(points a b) in
  let l2 := Q.(points a b) in
  exists (R : partition_R a b), List.incl l1 (R.(points a b)) /\ List.incl l2 (R.(points a b)).
Proof.
  intros a b P Q l1 l2. set (l3 := get_all_points l1 l2). set (l4 := get_all_points l2 l1).
  set (l5 := add_points_Sorted_Rlt l1 l3). set (l6 := add_points_Sorted_Rlt l5 l3).
  assert (H1 : a < b). { pose proof partition_spec a b P; tauto. }
  assert (H3 : Sorted Rlt l6). { admit. }
  assert (H4 : List.In a l6). { admit. }
  assert (H5 : List.In b l6). { admit. }
  assert (H6 : forall x, List.In x l6 -> a <= x <= b). { admit. }
  set (R := mkRpartition a b l6 H1 H3 H4 H5 H6). exists R. split.
  - simpl. intros r H7. admit.
  - simpl. intros r H7. admit.
Admitted.

Theorem theorem_13_1_a : forall (a b : ℝ) (f : bounded_function_R a b) (P1 P2 : partition_R a b),
  L(f, P1(a, b)) <= U(f, P2(a, b)).
Proof.
  intros a b f P1 P2. pose proof exists_partition_R_includes_both a b P1 P2 as [R [H1 H2]].
  specialize (lemma_13_1_a a b f R P1 H1) as H3. specialize (lemma_13_1_b a b f R P2 H2) as H4.
  specialize (lower_sum_le_upper_sum a b f R) as H5. lra.
Qed.

Theorem theorem_13_1_b : forall (a b : ℝ) (f : bounded_function_R a b) (P1 P2 : partition_R a b),
  U(f, P1(a, b)) >= L(f, P2(a, b)).
Proof.
  intros a b f P1 P2. pose proof exists_partition_R_includes_both a b P1 P2 as [R [H1 H2]].
  specialize (lemma_13_1_a a b f R P2 H2) as H3. specialize (lemma_13_1_b a b f R P1 H1) as H4.
  specialize (lower_sum_le_upper_sum a b f R) as H5. lra.
Qed.

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

Example small_bulls : forall x, x = 3.21 -> x^2 - 1.1 = 9.2041.
Proof. intros x H1. subst. lra. Qed.

Lemma lt_eps_same_number : forall a b,
  b >= a -> (forall ε, ε > 0 -> b - a < ε) -> a = b.
Proof.
  intros a b H1 H2. pose proof Rtotal_order a b as [H3 | [H3 | H3]]; auto; try lra.
  specialize (H2 (b - a) ltac:(lra)). lra.
Qed.

Theorem theorem_13_2 : forall (a b : ℝ) (f : bounded_function_R a b),
  Integrable_On f.(Integrals.f a b) a b <-> (forall ε, ε > 0 -> exists P : partition_R a b, (U(f, P(a, b)) - L(f, P(a, b))) < ε).
Proof.
  intros a b f. split.
  - intros [bf [sup [inf [H1 [H2 [H3 H4]]]]]] ε H5. replace bf with f in *.
    2 : { destruct bf, f. simpl in *. subst. f_equal; apply proof_irrelevance. } clear H1.
    set (α := sup). replace inf with α in *. replace sup with α in *. clear H4.
    set (E1 := λ x : ℝ, ∃ p : partition_R a b, x = (L(f, p(a, b)))). set (E2 := λ x : ℝ, ∃ p : partition_R a b, x = (U(f, p(a, b)))).
    pose proof lub_eq_glb_diff_lt_eps E1 E2 α ε ltac:(auto) ltac:(auto) H5 as [x1 [x2 [H6 [H7 H8]]]].
    assert (exists (P' : partition_R a b), x1 = L(f, P'(a, b))) as [P' H9] by auto. 
    assert (exists (P'' : partition_R a b), x2 = U(f, P''(a, b))) as [P'' H10] by auto.
    assert (U(f, P''(a, b)) - (L(f, P'(a, b))) < ε) as H11 by lra.
    pose proof exists_partition_R_includes_both a b P' P'' as [P [H12 H13]].
    exists P.
    assert (U(f, P''(a, b)) >= (U(f, P(a, b)))) as H14. { apply lemma_13_1_b with (P := P''); auto. }
    assert (L(f, P'(a, b)) <= (L(f, P(a, b)))) as H15. { apply lemma_13_1_a with (P := P'); auto. }
    lra.
  - intros H1. simpl. set (E1 := λ x : ℝ, ∃ P : partition_R a b, x = (L(f, P(a, b)))).
    set (E2 := λ x : ℝ, ∃ P : partition_R a b, x = (U(f, P(a, b)))).
    assert (H2 : ∃ x, E1 x). { specialize (H1 1 ltac:(lra)) as [P H1]. exists (L(f, P(a, b))). exists P. auto. }
    assert (H3 : has_upper_bound E1).
    { unfold has_lower_bound. specialize (H2) as [x1 [P H2]]. exists (U(f, P(a, b))). intros x2 [P' H3]. subst. apply theorem_13_1_a. }
    assert (H4 : E1 ≠ ∅). { apply not_Empty_In; auto. } pose proof completeness_upper_bound E1 H3 H4 as [sup H5]. 
    assert (H6 : ∃ x, E2 x). { specialize (H1 1 ltac:(lra)) as [P H1]. exists (U(f, P(a, b))). exists P. auto. }
    assert (H7 : has_lower_bound E2).
    { unfold has_lower_bound. specialize (H6) as [x1 [P H6]]. exists (L(f, P(a, b))). intros x2 [P' H7]. subst. apply theorem_13_1_b. }
    assert (H8 : E2 ≠ ∅). { apply not_Empty_In; auto. } pose proof completeness_lower_bound E2 H7 H8 as [inf H9].
    assert (H10 : forall ε, ε > 0 -> inf - sup < ε).
    { intros ε H10. specialize (H1 ε H10) as [P H1]. pose proof glb_lt_In E2 inf (U(f, P(a, b))) H9 ltac:(exists P; auto) as H11.
      pose proof lub_gt_In E1 sup (L(f, P(a, b))) H5 ltac:(exists P; auto) as H12. lra.
    }
    assert (H11 : sup <= inf). { apply (sup_le_inf E1 E2); auto. intros x y [P H11] [P' H12]. subst. apply theorem_13_1_a. }
    pose proof lt_eps_same_number sup inf ltac:(lra) H10 as H12.
    exists f, sup, inf; repeat (split; auto).
Qed.

Theorem theorem_13_3 : forall f a b,
  continuous_on f [a, b] -> Integrable_On f a b.
Proof.
  
Qed.


Theorem FTC1 : ∀ f F a b,
  (∀ x, x ∈ [a, b] -> ∫ a x f = (F x)) -> continuous_on f [a, b] -> ⟦ der ⟧ F ⦅a, b⦆ = f.
Proof.
  intros f F a b H1 H2 c H3. unfold derivative_at.
  assert (H4 : forall h, h ∈ ⦅0, (b - c)⦆ -> ∫ a (c + h) f - ∫ a c f = (F (c + h) - F c)).
  { 
    intros h H4. specialize (H1 (c + h) ltac:(unfold Ensembles.In in *; lra)) as H5. 
    specialize (H1 c ltac:(unfold Ensembles.In in *; lra)) as H6. exists (F (c + h)), (F c). split; auto.
  }
Admitted.