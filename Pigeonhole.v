Require Import Imports List.

Inductive count_occ_of {A : Type} (x : A) : list A -> nat -> Prop :=
  | count_nil : count_occ_of x nil 0
  | count_cons_eq : forall l n h, count_occ_of x l n -> x = h -> count_occ_of x (h :: l) (S n)
  | count_cons_neq : forall l n h, count_occ_of x l n -> x <> h -> count_occ_of x (h :: l) n.

Lemma count_occ_of_cons : forall (A : Type) (l : list A) (x h : A) (n : nat),
  count_occ_of x l n -> (x = h -> count_occ_of x (h :: l) (S n)) /\ (x <> h -> count_occ_of x (h :: l) n).
Proof.
  intros A l x h n H1. induction H1 as [| l n h' H1 [IH1 IH2] | l n h' H1 [IH1 IH2]].
  - split; intros H1; subst; repeat (constructor; auto).
  - split; intro H2.
    -- specialize (IH1 H2). subst. constructor; auto.
    -- specialize (IH2 H2). subst. apply count_cons_neq; auto. apply count_cons_eq; auto.
  - split; intros H2.
    -- specialize (IH1 H2). subst. apply count_cons_eq; auto. apply count_cons_neq; auto.
    -- specialize (IH2 H2). subst. apply count_cons_neq; auto. apply count_cons_neq; auto.
Qed.

Lemma count_occ_of_In : forall (A : Type) (l : list A) (x : A) (n : nat),
  count_occ_of x l n -> (n > 0)%nat -> In x l.
Proof.
  intros A l x n H1 H2. induction H1.
  - lia.
  - simpl. left. auto.
  - simpl. right. apply IHcount_occ_of. lia.
Qed.

Lemma In_count_occ_of : forall (A : Type) (l : list A) (x : A) (n : nat),
  In x l -> count_occ_of x l n -> (n > 0)%nat.
Proof.
  intros A l x n H1 H2. induction H2.
  - inversion H1.
  - destruct H1 as [H1 | H1].
    -- subst. lia.
    -- specialize (IHcount_occ_of H1). lia.
  - apply IHcount_occ_of. destruct H1; auto; subst; contradiction.
Qed.

Lemma not_In_count_occ_of : forall (A : Type) (l : list A) (x : A),
  ~ In x l -> count_occ_of x l 0.
Proof.
  intros A l x H1. induction l as [| h t IH].
  - constructor.
  - constructor.
    -- apply IH. intros H2. apply H1. right. auto.
    -- intros H2. apply H1. left. auto.
Qed.

Lemma count_occ_of_unicity : forall (A : Type) (l : list A) (x : A) (n1 n2 : nat),
  count_occ_of x l n1 -> count_occ_of x l n2 -> n1 = n2.
Proof.
  intros A l x n1 n2 H1. revert n2. induction H1.
  - intros n2 H2. inversion H2; auto.
  - intros n2 H2. inversion H2; subst; try contradiction. rewrite (IHcount_occ_of n0); auto.
  - intros n2 H2. inversion H2; subst; try contradiction. rewrite (IHcount_occ_of n2); auto.
Qed.

Lemma count_occ_of_cons_neq : forall (A : Type) (l : list A) (x h : A) (n : nat),
  count_occ_of x l n -> x <> h -> count_occ_of x (h :: l) n.
Proof.
  intros A l x h n H1 H2. induction H1.
  - constructor; auto. constructor.
  - apply count_cons_neq; auto. apply count_cons_eq; auto.
  - apply count_cons_neq; auto. apply count_cons_neq; auto.
Qed.

Lemma count_occ_of_cons_neq_inv : forall (A : Type) (l : list A) (x h : A) (n : nat),
  count_occ_of x (h :: l) n -> x <> h -> count_occ_of x l n.
Proof.
  intros A l x h n H1 H2. induction l.
  - inversion H1; subst; try contradiction; auto.
  - inversion H1. subst; try contradiction. auto.
Qed.

Lemma count_occ_of_cons_eq : forall (A : Type) (l : list A) (x h : A) (n : nat),
  count_occ_of x l n -> x = h -> count_occ_of x (h :: l) (S n).
Proof.
  intros A l x h n H1 H2. induction H1.
  - constructor; auto. constructor.
  - apply count_cons_eq; auto. apply count_cons_eq; auto.
  - apply count_cons_eq; auto. apply count_cons_neq; auto.
Qed.

Lemma count_occ_of_cons_eq_inv : forall (A : Type) (l : list A) (x h : A) (n : nat),
  count_occ_of x (h :: l) (S n) -> x = h -> count_occ_of x l n.
Proof.
  intros A l x h n H1 H2. induction l.
  - inversion H1; subst; try contradiction; auto.
  - inversion H1. subst; try contradiction; auto. tauto.
Qed.

Lemma exists_count_occ_of : forall (A : Type) (l : list A) (x : A),
  In x l -> exists n, count_occ_of x l n /\ (n > 0)%nat.
Proof.
  intros A l x H1. induction l as [| h l' IH].
  - inversion H1.
  - destruct H1 as [H1 | H1].
    -- pose proof classic (In x l') as [H2 | H2].
       * specialize (IH H2) as [n [H3 _]]. exists (S n). split; try lia. apply count_occ_of_cons_eq; auto.
       * exists 1%nat. subst. constructor; auto. apply not_In_count_occ_of in H2; auto. constructor; auto.
    -- pose proof classic (x = h) as [H2 | H2].
       * specialize (IH H1) as [n H3]. exists (S n). split; try lia. apply count_occ_of_cons_eq; tauto.
       * specialize (IH H1) as [n H3]. exists n. split; try lia. apply count_occ_of_cons_neq; tauto.
Qed.

Lemma exists_remove_one : forall (A : Type) (l : list A) (x : A) (n : nat),
  In x l -> count_occ_of x l n -> exists l', count_occ_of x l' (n - 1)%nat /\
    (forall y n', y <> x -> count_occ_of y l n' -> count_occ_of y l' n') /\ (length l' = length l - 1)%nat.
Proof.
  intros A l x n H1 H2. induction H2.
  - inversion H1.
  - destruct H1 as [H1 | H1].
    -- exists l. repeat split. replace (S n - 1)%nat with n by lia. auto.
       intros y n2 H3 H4. inversion H4; auto; subst; contradiction.
       simpl. lia.
    -- specialize (IHcount_occ_of H1) as [l' [H3 [H4 H5]]].
       exists (h :: l'). repeat split; subst.
       * apply count_occ_of_cons with (h := h) in H3 as [H3 _]. specialize (H3 eq_refl). auto.
         assert (n = 0 \/ n > 0)%nat as [H6 | H6] by lia.
         ** apply In_count_occ_of with (n := n) in H1; auto. lia.
         ** replace (S n - 1)%nat with (S (n - 1))%nat by lia. auto.
       * intros y n2 H6 H7. specialize (H4 y n2 H6). apply count_occ_of_cons; auto. apply H4. inversion H7; auto. subst; contradiction.
       * simpl. assert (length l > 0)%nat as H6. { destruct l. inversion H1. simpl. lia. } lia.
  - destruct H1 as [H1 | H1]; subst; try contradiction. specialize (IHcount_occ_of H1) as [l' [H3 [H4 H5]]].
    exists (h :: l'). repeat split; subst.
    -- apply count_occ_of_cons with (h := h) in H3 as [_ H3]. apply H3. auto.
    -- intros y n2 H6 H7. pose proof classic (y = h) as [H8 | H8].
       * subst. inversion H7; auto; subst; try contradiction. specialize (H4 h n0 H6 H9).
         apply count_occ_of_cons with (h := h) in H4 as [H4 _]. apply H4. auto.
       * apply count_occ_of_cons; auto. apply H4; auto. inversion H7; auto; subst; contradiction.
    -- simpl. assert (length l > 0)%nat as H6. { destruct l. inversion H1. simpl. lia. } lia.
Qed.

Lemma count_occ_eq_len : forall (A : Type) (l1 l2 : list A),
  (forall x n, count_occ_of x l1 n /\ count_occ_of x l2 n) -> length l1 = length l2.
Proof.
  intros A l1. induction l1 as [| h1 t1 IH].
  - intros l2 H1. simpl. destruct l2; auto. specialize (H1 a 0%nat). destruct H1 as [_ H1].
    inversion H1. tauto.
  - intros l2 H1. destruct l2 as [| h2 t2].
    + simpl. specialize (H1 h1 0%nat) as [H1 _]. inversion H1; contradiction.
    + simpl. apply eq_S. pose proof classic (h1 = h2) as [H2 | H2].
      * apply IH. intros x n. specialize (H1 x). assert (h1 = x \/ h1 <> x) as [H3 | H3] by apply classic.
        -- subst. specialize (H1 (S n)) as [H1 H2]. inversion H1; inversion H2; tauto.
        -- specialize (H1 n) as [H1 H4]. subst. apply count_occ_of_cons_neq_inv in H1, H4; auto.
      * assert (length t2 = 0 \/ length t2 > 0)%nat as [H3 | H3] by lia.
        -- rewrite length_zero_iff_nil in H3. subst. specialize (H1 h1 0%nat) as [H1 _]. inversion H1; contradiction.
        -- pose proof classic (In h1 t2) as [H4 | H4].
           ++ pose proof exists_count_occ_of A t2 h1 H4 as [n [H5 H6]]. pose proof exists_remove_one A t2 h1 n H4 H5 as [l [H7 [H8 H9]]].
              specialize (IH (h2 :: l)). rewrite IH. simpl. rewrite H9. lia. intros x n'. pose proof classic (x = h1) as [H10 | H10].
              ** specialize (H1 x (S n')). split. specialize H1 as [H1 _]. apply count_occ_of_cons_eq_inv in H1; auto.
                 destruct H1 as [_ H1]. subst. apply count_occ_of_cons_neq; auto. apply count_occ_of_cons_neq_inv in H1; auto.
                 assert (n = S n') as H10. { apply (count_occ_of_unicity A t2 h1); auto. } replace n' with (n - 1)%nat by lia. auto.
              ** specialize (H1 x n') as [H1 H1']. apply count_occ_of_cons_neq_inv in H1; auto. split; auto. pose proof classic (x = h2) as [H11 | H11].
                 --- subst. inversion H1'; try contradiction. apply count_occ_of_cons_eq; auto.
                 --- specialize (H8 x n' ltac:(auto)). apply count_occ_of_cons_neq_inv in H1'; auto. apply count_occ_of_cons_neq; auto.
          ++ apply IH. intros x n. pose proof classic (x = h1) as [H10 | H10].
             ** subst. specialize (H1 h1 0%nat) as [H1 H1']. inversion H1; inversion H1'; tauto.
             ** specialize (H1 h1 0%nat) as [H1 H1']. inversion H1; inversion H1'; tauto.
Qed.

Lemma list_has_len : forall (U : Type) (l : list U) (a : U),
  In a l -> (length l > 0)%nat.
Proof.
  intros U l a. induction l as [| h l' IH].
  - simpl. lia.
  - simpl. intros [H1 | H1]; lia.
Qed.

Lemma in_notin_neq : forall (A : Type) (l : list A) x1 x2,
  In x1 l -> ~ (In x2 l) -> x1 <> x2.
Proof.
  intros A l x1 x2 H1 H2. induction l as [| h l' IH].
  - inversion H1.
  - simpl in *. destruct H1 as [H1 | H1].
    -- rewrite H1 in H2. tauto.
    -- tauto.
Qed.

Theorem longer_list:
    forall U : Type, forall l1 l2 : list U,
    (forall x, In x l1 -> In x l2) ->
    (exists x, In x l2 /\ ~ In x l1) ->
    NoDup l1 ->
    (length l2 > length l1)%nat.
Proof.
  intros U l1 l2 H1 H2 H3. generalize dependent l2.
  induction l1 as [| h l1' IH].
  - intros l2 H4 H5. simpl in *. destruct H5 as [x H5]. assert (exists a, In a l2) as [a H6].
  { exists x. apply H5. } apply list_has_len in H6. lia.
  - intros l2 H4 [a [H5 H6]]. apply NoDup_cons_iff in H3. destruct H3 as [H3 H3'].
    pose proof (exists_count_occ_of U l2 a H5) as [n [H7 _]]. pose proof (exists_remove_one U l2 a n H5 H7) as [l2' [H8 [H9 H10]]].
    specialize (IH H3' l2'). apply not_in_cons in H6 as [H6 H6'].
    assert (In h l2') as H11.
    { 
      specialize (H4 h ltac:(simpl; auto)). apply exists_count_occ_of in H4 as [n' [H11 H12]]. specialize (H9 h n' ltac:(auto) H11).
      apply count_occ_of_In with (n := n'); auto. 
    }
    assert (length l2' > length l1')%nat as H12.
    { 
      apply IH. 2 : { exists h; auto. } intros x H12. specialize (H4 x ltac:(simpl; auto)).
      assert (x <> a) as H13. { apply in_notin_neq with (l := l1'); auto. }
      pose proof (exists_count_occ_of U l2 x H4) as [n' [H14 H15]]. specialize (H9 x n' H13 H14). 
      apply count_occ_of_In with (n := n'); auto.
    }
    simpl; lia.
Qed.

Theorem pigeonhole_principle_list : forall (U : Type) (l1 l2 : list U),
  (forall x, In x l1 -> In x l2) -> (length l2 < length l1)%nat ->
    ~ NoDup l1.
Proof.
  intros U l1. induction l1 as [|a l1' IH].
  - simpl. lia.
  - simpl. intros l2 H1 H2. pose proof classic (List.In a l1') as [H3 | H3].
    -- intros H4. apply NoDup_cons_iff in H4 as [H4 H5]. tauto.
    -- intros H4. apply IH with (l2 := l2).
       3 : { apply NoDup_cons_iff in H4. tauto. }
       intros x H5. specialize (H1 x). assert (a = x \/ In x l1') as H6 by tauto. tauto.
       assert (H5 : (length l2 > length l1')%nat).
       { apply longer_list. intros x H5. apply (H1 x). tauto. exists a. split. apply (H1 a).
        tauto. tauto. apply NoDup_cons_iff in H4. tauto. }
       lia.
Qed.