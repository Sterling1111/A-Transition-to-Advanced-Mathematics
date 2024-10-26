Require Import Lia ZArith Classical.

Open Scope nat_scope.

Definition induction_nat := forall P : nat -> Prop,
  (P 0 /\ (forall k : nat, P k -> P (S k))) -> forall n, P n.

Definition strong_induction_nat := forall P : nat -> Prop,
  (forall m, (forall k : nat, k < m -> P k) -> P m) -> forall n, P n.

Definition well_ordering_nat := forall E : nat -> Prop,
  (exists x, E x) -> (exists n, E n /\ forall m, E m -> (n <= m)).

Definition well_ordering_principle_contrapositive_nat := forall E : nat -> Prop,
  (~(exists m, E m /\ forall k, E k -> m <= k)) -> (~(exists n, E n)).

Lemma induction_imp_induction_nat : induction_nat.
Proof.
  unfold induction_nat. intros P [H_base H_ind] n.
  induction n as [| k IH].
  - apply H_base.
  - apply H_ind. apply IH.
Qed.

Lemma lemma_2_10 : well_ordering_nat -> induction_nat.
Proof.
  unfold well_ordering_nat, induction_nat. intros well_ordering_nat P [Hbase H_inductive] n.
  set (E := fun m => ~ P m).
  specialize (well_ordering_nat E). assert (H1 : forall n : nat, E n -> False).
  - intros x H1. assert (H3 : exists x, E x) by (exists x; auto). apply well_ordering_nat in H3.
    destruct H3 as [least_elem_E H3]. destruct H3 as [H3 H4]. specialize (H_inductive (least_elem_E - 1)).
    destruct least_elem_E as [| least_elem_E'].
    -- apply H3. apply Hbase.
    -- specialize (H4 least_elem_E'). assert (H5 : S least_elem_E' <= least_elem_E' -> False) by lia.
       assert (H6 : ~(E least_elem_E')) by tauto. unfold E in H6. simpl in *. rewrite Nat.sub_0_r in *.
       apply NNPP in H6. apply H_inductive in H6. apply H3. apply H6.
  - specialize (H1 n). unfold E in H1. apply NNPP in H1. apply H1.
Qed.

Lemma lemma_2_11 : induction_nat -> strong_induction_nat.
Proof.
  unfold induction_nat, strong_induction_nat. intros induction_nat P H1 n.
  assert (H2 : forall k, k <= n -> P k).
  - apply induction_nat with (n := n). split.
    -- intros k Hk. inversion Hk. apply H1. intros k' Hk'. inversion Hk'.
    -- intros k Hk. intros k' Hk'. apply H1. intros k'' Hk''. apply Hk. lia.
  - apply H2. lia.
Qed.

Lemma strong_induction_nat_imp_well_ordering_contrapositive_nat : strong_induction_nat -> well_ordering_principle_contrapositive_nat.
Proof.
  intros H1 E H2. set (E' := fun n => ~ E n). assert (~ E 0) as H3.
  { intros H3. apply H2. exists 0. split; auto; lia. }
  assert (H4 : forall n, E' n).
  {
    intros n. apply H1. intros m H4. destruct m.
    - unfold E'. intros H5. apply H3. apply H5.
    - assert (E (S m) -> False) as H5.
      { 
        intros H5. apply H2. exists (S m). split; auto. intros k H6.
        specialize (H4 k). assert (E' k -> False) as H7; auto. assert (k < S m -> False) as H8 by auto. lia.
      }
      auto.
  }
  intros [n H5]. apply (H4 n). auto.
Qed.

Lemma strong_induction_nat_imp_well_ordering_nat : strong_induction_nat -> well_ordering_nat.
Proof.
  intros H1. specialize (strong_induction_nat_imp_well_ordering_contrapositive_nat H1) as H2.
  clear H1. rename H2 into H1. intros E H2. 
  assert (H3 : ~(exists m, E m /\ forall k, E k -> m <= k) -> ~(exists n, E n)) by apply H1.
  destruct (classic (exists m, E m /\ forall k, E k -> m <= k)) as [H4 | H4]; auto.
  exfalso. apply H3 in H4. apply H4. apply H2.
Qed.

Lemma WI_SO_WO_equiv : (well_ordering_nat <-> strong_induction_nat) /\ (strong_induction_nat <-> induction_nat) /\ (induction_nat <-> well_ordering_nat).
Proof.
  pose proof lemma_2_10 as H1. pose proof lemma_2_11 as H2. pose proof (strong_induction_nat_imp_well_ordering_nat) as H3. tauto.
Qed.

Lemma WI_SI_WO :  induction_nat /\ strong_induction_nat /\ well_ordering_nat.
Proof.
  pose proof WI_SO_WO_equiv as H1. pose proof (induction_imp_induction_nat) as H2. tauto.
Qed. 

Lemma strong_induction_N : strong_induction_nat.
Proof.
  apply lemma_2_11. apply induction_imp_induction_nat.
Qed.

Ltac strong_induction_nat n :=
  intros;
  repeat match goal with
         | [ H : _ |- _ ] =>
           lazymatch H with
           | n => fail (* Do not revert n *)
           | _ => revert H
           end
         end;
  (* Apply strong induction on n *)
  apply strong_induction_N with (n := n);
  (* Clear n from context *)
  clear n;
  (* Introduce n and IH *)
  intros n IH.

Close Scope nat_scope.

Open Scope Z_scope.

Lemma Z_ind_pos:
  forall (P: Z -> Prop),
  P 0 ->
  (forall z, z >= 0 -> P z -> P (z + 1)) ->
  forall z, z >= 0 -> P z.
Proof.
  intros P H0 Hstep z Hnonneg.

  (* Convert the problem to induction over natural numbers *)
  remember (Z.to_nat z) as n eqn:Heq.
  assert (Hnneg: forall n : nat, P (Z.of_nat n)).
  {
    intros n1. induction n1.
    - simpl. apply H0.
    - replace (S n1) with (n1 + 1)%nat by lia.
      rewrite Nat2Z.inj_add. apply Hstep. lia. apply IHn1.
  }

  specialize(Hnneg n). rewrite Heq in Hnneg.
  replace (Z.of_nat (Z.to_nat z)) with (z) in Hnneg. apply Hnneg.
  rewrite Z2Nat.id. lia. lia.
Qed.

Lemma Z_induction_bidirectional :
  forall P : Z -> Prop,
  P 0 ->
  (forall n : Z, P n -> P (n + 1)) ->
  (forall n : Z, P n -> P (n - 1)) ->
  forall n : Z, P n.
Proof.
  intros P H0 Hpos Hneg n.

  assert (Hnneg: forall n : nat, P (Z.of_nat n)).
  {
    intros n1. induction n1.
    - simpl. apply H0.
    - replace (S n1) with (n1 + 1)%nat by lia.
      rewrite Nat2Z.inj_add. apply Hpos. apply IHn1.
  }

  destruct (Z_lt_le_dec n 0).
  - replace n with (- Z.of_nat (Z.to_nat (- n))) by
      (rewrite Z2Nat.id; lia).
    induction (Z.to_nat (-n)).
    + simpl. apply H0.
    + replace (S n0) with (n0 + 1)%nat by lia. rewrite Nat2Z.inj_add.
      replace (- (Z.of_nat n0 + Z.of_nat 1)) with (-Z.of_nat n0 - 1) by lia. apply Hneg. apply IHn0.
  - apply Z_ind_pos.
    -- apply H0.
    -- intros z H. apply Hpos.
    -- lia.
Qed.

Lemma strong_induction_Z :
  forall P : Z -> Prop,
  (forall m, (forall k : Z, 0 <= k < m -> P k) -> P m) ->
  forall n, 0 <= n -> P n.
Proof.
  intros P H1 n H2. assert (H3: forall k, 0 <= k < n -> P k).
  - apply Z_induction_bidirectional with (n := n).
    -- lia.
    -- intros z H. intros k Hk. apply H1. intros k' Hk'. apply H. lia.
    -- intros z H. intros k Hk. apply H1. intros k' Hk'. apply H. lia.
  - apply H1. intros k Hk. apply H3. lia.
Qed.

Ltac strong_induction_Z_pos z :=
  intros;
  let H2 := fresh "H" in
  assert (H2 : 0 <= z) by nia;
  repeat match goal with
         | [ H : _ |- _ ] =>
           lazymatch H with
           | H2 => fail
           | z => fail
           | _ => revert H
           end
         end;
  apply strong_induction_Z with (n := z); try lia;
  clear H2; clear z; intros z IH H1.

Ltac strong_induction T :=
match type of T with
| nat => strong_induction_nat T
| Z => strong_induction_Z_pos T
| _ => fail "unsupported type"
end.

Lemma well_ordering_principle_contrapositive_Z : forall E : Z -> Prop,
  (forall n : Z, E n -> n >= 0) ->
  (~(exists m, E m /\ forall k, k >= 0 -> E k -> m <= k)) ->
    (~(exists n, E n)).
Proof.
  intros E Hnon_neg H.
  set (E' := fun z => ~ E z).
  assert (E 0 -> False).
  { intros H2. apply H. exists 0. split; try split.
    - apply H2.
    - intros k _ H3. specialize (Hnon_neg k). apply Hnon_neg in H3. lia.
  }
  assert (H2: forall z, z >= 0 -> E' z).
  {
    intros z Hz. apply strong_induction_Z. intros m H2. destruct (Z_le_dec m 0).
    - unfold E'. unfold not. apply Z_le_lt_eq_dec in l. destruct l.
      -- specialize (Hnon_neg m). intros H3. apply Hnon_neg in H3. lia.
      -- rewrite e. apply H0.
    - assert (E m -> False).
      { intros H3. apply H. exists m. split; try split.
        - apply H3.
        - intros k H4 H5. specialize (H2 k). assert (E' k -> False). unfold E'.
          unfold not. intros H6. apply H6. apply H5. assert (0 <= k < m -> False) by auto.
          lia.
      }
      unfold E'. unfold not. apply H1.
    - lia.
  }
  unfold E' in H2. unfold not in H2. unfold not. intros H3. destruct H3 as [n H3].
  specialize (H2 n). apply H2. apply Hnon_neg in H3. apply H3. apply H3.
Qed.

Theorem well_ordering_Z : forall E : Z -> Prop,
  (forall z, E z -> z >= 0) ->
  (exists x, E x) ->
  (exists n, E n /\ forall m, m >= 0 -> E m -> (n <= m)).
Proof.
  intros E Hnon_neg [x Ex].
  assert (H :
    (forall n : Z, E n -> n >= 0) ->
      (~(exists m, E m /\ forall k, k >= 0 -> E k -> m <= k)) ->
      (~(exists n, E n))).
    { apply well_ordering_principle_contrapositive_Z. }

  destruct (classic (exists m, E m /\ forall k, k >= 0 -> E k -> m <= k)) as [C1|C2].
  - apply C1.
  - exfalso. apply H in C2. apply C2. exists x. apply Ex. apply Hnon_neg.
Qed.