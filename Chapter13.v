Require Import ZArith Lia Classical Reals Lra Classical_sets List Ensembles QArith ClassicalFacts Finite_sets Finite_sets_facts Sums Sets WI_SI_WO.
Require Export Chapter12.
Import ListNotations SetNotations.

Open Scope R_scope.

Ltac break_INR :=
  repeat match goal with
  | [ |- context[INR (?n + ?m)] ] =>
      rewrite plus_INR
  | [ |- context[INR (?n * ?m)] ] =>
      rewrite mult_INR
  | [ |- context[INR (S ?n)] ] =>
      rewrite S_INR
  | [ |- context[INR (?n - ?m)] ] =>
      rewrite minus_INR
  end.

Ltac convert_nat_to_INR_in_H :=
  try
  match goal with
  | [ H: (?x > ?y)%nat |- _ ] => apply lt_INR in H; simpl in H
  | [ H: (?x < ?y)%nat |- _ ] => apply lt_INR in H; simpl in H
  | [ H: (?x >= ?y)%nat |- _ ] => apply le_INR in H; simpl in H
  | [ H: (?x <= ?y)%nat |- _ ] => apply le_INR in H; simpl in H
  | [ H: (?x = ?y)%nat |- _ ] => apply INR_eq in H; simpl in H
  end.

Ltac solve_INR :=
  convert_nat_to_INR_in_H; try field_simplify_eq; try break_INR; simpl; try field; try nra; try lia.

Lemma lemma_13_1 : forall (n : ℕ),
  sum_f 0 n (fun i => INR (2 * i - 1)) = INR (n^2).
Proof.
  induction n as [| k IH].
  - compute. lra.
  - rewrite sum_f_i_Sn_f; try lia. rewrite IH. replace (S k^2)%nat with (k^2 + 2 * k + 1)%nat. 2 : { simpl. lia. }
    replace (2 * S k - 1)%nat with (2 * k + 1)%nat by lia. solve_INR.
Qed.

Lemma lemma_13_1' : forall (n : ℕ),
  (n > 0)%nat -> sum_f 1 n (fun i => INR (2 * i - 1)) = INR (n^2).
Proof.
  intro n. set (P := fun n => (n > 0)%nat -> sum_f 1 n (fun i => INR (2 * i - 1)) = INR (n^2)).
  assert (((P 0%nat /\ (forall k : ℕ, P k -> P (S k))) -> forall n : ℕ, P n)) as H1.
  { apply induction_imp_induction_nat. } assert (forall n, P n) as H2.
  {
    apply H1. split.
    - unfold P. intros H2. lia.
    - intros k IH. unfold P in IH. unfold P. intros H2. assert (k = 0 \/ (k > 0))%nat as [H3 | H3] by lia.
      -- rewrite H3. rewrite sum_f_n_n. simpl. lra.
      -- rewrite sum_f_i_Sn_f; try lia. specialize (IH H3). rewrite IH. replace (S k^2)%nat with (k^2 + 2 * k + 1)%nat. 2 : { simpl. lia. }
         replace (2 * S k - 1)%nat with (2 * k + 1)%nat by lia. solve_INR.
  }
  specialize (H2 n). unfold P in H2. apply H2.
Qed.

Open Scope R_scope.

Lemma lemma_13_2 : forall (n : ℕ),
  (n > 0)%nat -> sum_f 1 n (fun i => 1 / (INR (2 * i - 1) * INR (2 * i + 1))) = INR n / INR (2 * n + 1).
Proof.
  intros n H1. induction n as [| k IH]; try lia. clear H1. assert (k = 0 \/ k > 0)%nat as [H1 | H1] by lia.
  - rewrite H1. compute. lra.
  - rewrite sum_f_i_Sn_f; try lia. rewrite (IH H1). solve_INR.
Qed.

Lemma lemma_13_3 : forall n : nat,
  (n > 0)%nat -> sum_f 1 n (fun i => INR i ^ 2) = (INR n * (INR n + 1) * (2 * INR n + 1)) / 6.
Proof.
  intros n H1. induction n as [| k IH]; try lia. assert (S k = 1 \/ k >= 1)%nat as [H2 | H2] by lia.
  - rewrite H2. compute. lra.
  - rewrite sum_f_i_Sn_f; try lia. rewrite IH; auto. solve_INR.
Qed.

Open Scope nat_scope.

Lemma lemma_13_a : forall n : ℕ,
  n > 0 -> n < 3^n.
Proof.
  intros n H1. induction n as [| k IH]; try lia. assert (k = 0 \/ k > 0) as [H2 | H2] by lia.
  - rewrite H2. compute. lia.
  - specialize (IH H2). replace (3^S k) with (3 * 3^k) by (simpl; lia). replace (S k) with (k + 1) by lia. lia.
Qed.

Open Scope Z_scope.

Lemma lemma_13_b : forall n : Z, n < 3^n.
Proof.
  intros n. assert (n = 0 \/ n > 0 \/ n < 0) as [H1 | [H1 | H1]] by lia.
  - rewrite H1. simpl. lia.
  - pose proof (lemma_13_a (Z.to_nat n)) as H2. assert (Z.to_nat n > 0)%nat as H3 by lia. specialize (H2 H3). apply inj_lt in H2.
    replace n with (Z.of_nat (Z.to_nat n)) at 1 by lia. rewrite inj_pow in H2. simpl in H2. rewrite Z2Nat.id in H2; lia.
  - assert (3^n = 0). { apply Z.pow_neg_r; lia. } lia.
Qed.

Open Scope R_scope.

Lemma lemma_13_5 : forall n r,
  r <> 1 -> sum_f 0 n (fun i => r ^ i) = (1 - r ^ (n+1)) / (1 - r).
Proof.
  intros n r H1. induction n as [| k IH].
  - compute. field. nra.
  - destruct k as [| k'] eqn : Ek.
    -- compute. field. nra.
    -- rewrite sum_f_i_Sn_f. 2 : { lia. }
       rewrite IH. rewrite <- Ek. apply Rmult_eq_reg_l with (r := (1 - r)).
       2 : { nra. }
       replace ((1 - r) * ((1 - r ^ (k + 1)) / (1 - r) + r ^ S k)) with (1 - r^(k+1) + r^S k - r * r^S k) by (field; nra).
       replace ((1 - r) * ((1 - r ^ (S k + 1)) / (1 - r))) with (1 - r^(S k + 1)) by (field; nra).
       replace (r^(S k + 1)) with (r * r ^ (S k)). 2 : { replace (S k + 1)%nat with (S (S k)) by lia. simpl. auto. }
       simpl. apply Rplus_eq_reg_r with (r := r * (r * r^k)).
       replace (1 - r ^ (k + 1) + r * r ^ k - r * (r * r ^ k) + r * (r * r ^ k)) with
               (1 - r ^(k+1) + r * r^k) by nra.
       replace (1 - r * (r * r ^ k) + r * (r * r ^ k)) with 1 by nra.
       replace (k+1)%nat with (S k) by lia. simpl. lra.
Qed.

Lemma Rpow_gt_0 : forall k r,
  r > 0 -> r ^ k > 0.
Proof.
  intros k r H1. induction k as [| k' IH].
  - simpl. lra.
  - simpl. nra.
Qed.

Lemma Rpow_lt_1 : forall r n,
  0 < r < 1 -> (n > 0)%nat -> r ^ n < 1.
Proof.
  intros r n [H1 H2] H3. induction n as [| k IH].
  - lia.
  - simpl. destruct k.
    -- simpl. lra.
    -- assert (r ^ S k < 1) by (apply IH; lia). nra.
Qed.

Lemma Rpow_gt_1 : forall r n,
  r > 1 -> (n > 0)%nat -> r ^ n > 1.
Proof.
  intros r n H1 H2. induction n as [| k IH].
  - lia.
  - simpl. destruct k.
    -- simpl. lra.
    -- assert (r ^ S k > 1) by (apply IH; lia). nra.
Qed.

Lemma lemma_13_6 : forall n h,
  h > -1 -> (1 + h) ^ n >= 1 + INR n * h.
Proof.
  intros n h H1. induction n as [| k IH].
  - simpl. lra.
  - replace (1 + INR (S k) * h) with (1 + INR k * h + h). 2 : { rewrite S_INR. lra. }
    apply Rge_le in IH. apply Rle_ge. apply Rmult_le_compat_r with (r := 1 + h) in IH; try lra.
    replace ((1 + h) ^ k * (1 + h)) with ((1 + h) ^ S k) in IH by (simpl; lra).
    replace ((1 + INR k * h) * (1 + h)) with (1 + INR k * h + h + INR k * h^2) in IH by lra.
    assert (0 <= INR k * h^2) as H2. { apply Rmult_le_pos. apply pos_INR. apply pow2_ge_0. } nra.
Qed.

Proposition prop_13_11 : forall (A : Ensemble R),
  A ≠ ∅ -> Finite_set A -> exists r, r ∈ A /\ forall r', r' ∈ A -> r <= r'.
Proof.
  intros A H1 [l H2]. generalize dependent A. induction l as [| h t IH].
  - intros A H1 H2. simpl in H2. rewrite H2 in H1. exfalso. apply H1. reflexivity.
  - intros A H1 H2. rewrite list_to_ensemble_cons in H2. set (T := list_to_ensemble t).
    assert (T = ∅ \/ T ≠ ∅) as [H3 | H3] by apply classic.
    -- unfold T in H3. rewrite H3 in H2. rewrite Union_comm in H2. rewrite Union_Identity in H2.
       exists h. split. rewrite set_equal_def in H2. specialize (H2 h) as [H2 _]. apply H2. apply In_singleton.
       intros r' H4. rewrite set_equal_def in H2. specialize (H2 r') as [_ H2]. specialize (H2 H4). apply Singleton_inv in H2. lra.
    -- specialize (IH (list_to_ensemble t) H3 eq_refl) as [r [IH1 IH2]]. assert (h <= r \/ h > r) as [H4 | H4] by lra.
        + exists h. split.
          ++ rewrite set_equal_def in H2. specialize (H2 h) as [H2 _]. apply H2. apply In_Union_def. left. apply In_singleton.
          ++ intros r' H5. specialize (IH2 r'). rewrite set_equal_def in H2. specialize (H2 r') as [_ H2]. specialize (H2 H5).
             apply In_Union_def in H2 as [H2 | H2].
             * apply Singleton_inv in H2. lra.
             * specialize (IH2 H2). lra.
        + exists r. split.
          ++ rewrite set_equal_def in H2. specialize (H2 r) as [H2 _]. apply H2. apply In_Union_def. right. apply IH1.
          ++ intros r' H5. rewrite set_equal_def in H2. specialize (H2 r') as [_ H2]. specialize (H2 H5). apply In_Union_def in H2 as [H2 | H2].
             * apply Singleton_inv in H2. lra.
             * apply IH2. apply H2.
Qed.

Lemma exists_nat_list_exists_R_list : forall (l : list ℕ),
  exists l' : list R, list_to_ensemble l' = list_to_ensemble (map INR l).
Proof.
  induction l as [| h t IH].
  - exists []. reflexivity.
  - destruct IH as [l' IH]. exists (INR h :: l'). simpl. rewrite IH. reflexivity.
Qed.

Open Scope nat_scope.

Lemma lemma_13_7_a : forall (A : Ensemble ℕ),
  A ≠ ∅ -> Finite_set A -> exists n, n ∈ A /\ forall n', n' ∈ A -> n <= n'.
Proof.
  intros A H1 [l H2]. destruct (exists_nat_list_exists_R_list l) as [l' H3]. specialize (prop_13_11 (list_to_ensemble l')).
  intros H4. assert (H5 : list_to_ensemble l' ≠ ∅). 
  { rewrite H3. apply list_to_ensemble_map_not_empty. apply list_to_ensemble_not_empty. rewrite H2. auto. }
   specialize (H4 H5) as [r [H6 H7]].
  - exists l'. auto.
  - assert (exists n : ℕ, INR n = r) as [n H8].
    {
      pose proof in_map_iff INR l r as [H8 _]. rewrite In_list_to_ensemble in H8.
      rewrite <- H3 in H8. specialize (H8 H6) as [x [H8 _]]. exists x. auto.
    }
    exists n. split.
    -- rewrite <- H2. apply In_list_to_ensemble. apply In_list_to_ensemble in H6. pose proof (in_map_iff) as H9. 
       specialize (H9 ℕ R INR l r). rewrite list_to_ensemble_eq_iff in H3. specialize (H3 r) as [H3 _]. specialize (H3 H6).
       destruct H9 as [H9 _]. specialize (H9 H3) as [x [H9 H10]]. replace n%nat with x%nat. auto. apply INR_eq. lra.
    -- intros n' H9. rewrite <- H2 in H9. apply In_list_to_ensemble in H9. apply INR_le. rewrite H8. apply H7. rewrite H3.
       apply In_list_to_ensemble. apply in_map_iff. exists n'; split; auto.
Qed.

Lemma lemma_13_7_b : forall (A : Ensemble ℕ),
  A ≠ ∅ -> ~Finite_set A -> exists n, n ∈ A /\ forall n', n' ∈ A -> n <= n'.
Proof.
  intros A H1 H2. pose proof (Empty_or_exists_In ℕ A) as [H3 | [n H3]]; try contradiction.
  set (B := list_to_ensemble (seq 0 (S n)) ⋂ A). assert (n ∈ B) as H4.
  { unfold B. apply In_Intersection_def. split; auto. apply In_list_to_ensemble. apply in_seq. lia. }
  assert (B ≠ ∅) as H5. { intros H5. rewrite H5 in H4. contradiction. }
  assert (H6 : Finite_set B). { apply Intersection_preserves_finite_2. unfold Finite_set. exists (seq 0 (S n)). reflexivity. }
  pose proof (lemma_13_7_a B H5 H6) as [m [H7 H8]]. exists m. split.
  - apply In_Intersection_def in H7. autoset.
  - intros n' H9. pose proof (In_or_not ℕ B n') as [H10 | H10].
    -- apply H8. autoset.
    -- assert (m <= n' \/ m > n') as [H11 | H11] by lia; try lia. exfalso. apply H10.
       apply In_Intersection_def. split; auto. apply In_list_to_ensemble. apply in_seq. specialize (H8 n H4). lia.
Qed.

Lemma lemma_13_7_c : forall (A : Ensemble ℕ),
  A ≠ ∅ -> exists n, n ∈ A /\ forall n', n' ∈ A -> n <= n'.
Proof.
  intros A H1. pose proof (classic (Finite_set A)) as [H2 | H2].
  - apply lemma_13_7_a; auto.
  - apply lemma_13_7_b; auto.
Qed.

Lemma count_occ_remove_neq : 
  forall (A : Type) (eq_dec : forall x y : A, sumbool (x = y) (x <> y)) (l : list A) (x y : A),
    x <> y -> count_occ eq_dec (remove eq_dec y l) x = count_occ eq_dec l x.
Proof.
  intros A A_eq_dec l x y H1. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (A_eq_dec y h) as [H2 | H2]; destruct (A_eq_dec h x) as [H3 | H3]; auto.
    -- exfalso. apply H1. rewrite <- H3. auto.
    -- simpl. destruct (A_eq_dec h x) as [H4 | H4]; auto; contradiction.
    -- simpl. destruct (A_eq_dec h x) as [H4 | H4]; auto; contradiction.
Qed.

Fixpoint remove_one {A : Type} (eq_dec : forall (x y : A), sumbool (x = y) (x <> y))
                        (a : A) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => if eq_dec x a then xs else x :: remove_one eq_dec a xs
  end.                    

Lemma remove_one_In : forall {A : Type} eq_dec (a : A) l,
  List.In a l -> count_occ eq_dec (remove_one eq_dec a l) a = pred (count_occ eq_dec l a).
Proof.
  intros A eq_dec a l H1. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct (eq_dec h a) as [H2 | H2].
    + simpl. reflexivity.
    + simpl. destruct H1 as [H1 | H1].
      * rewrite H1 in H2. contradiction.
      * rewrite IH; auto. destruct (eq_dec h a) as [H3 | H3]; try contradiction. reflexivity.
Qed.

Lemma remove_one_In_length : forall {A : Type} eq_dec (a : A) l,
  List.In a l -> length (remove_one eq_dec a l) = pred (length l).
Proof.
  intros A eq_dec a l H1. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct (eq_dec h a) as [H2 | H2].
    + simpl. reflexivity.
    + simpl. destruct H1 as [H1 | H1].
      * rewrite H1 in H2. contradiction.
      * rewrite IH; auto. destruct t.
        -- inversion H1.
        -- simpl. reflexivity.
Qed.

Lemma remove_one_not_In : forall {A : Type} eq_dec (a : A) l,
  ~List.In a l -> remove_one eq_dec a l = l.
Proof.
  intros A eq_dec a l H1. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (eq_dec h a) as [H2 | H2].
    + rewrite H2 in H1. rewrite not_in_cons in H1. tauto.
    + simpl. rewrite IH; auto. rewrite not_in_cons in H1. tauto.
Qed.

Lemma count_occ_remove_one_not_eq : forall {A : Type} eq_dec (a b : A) l,
  a <> b -> count_occ eq_dec (remove_one eq_dec a l) b = count_occ eq_dec l b.
Proof.
  intros A eq_dec a b l H1. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (eq_dec h a) as [H2 | H2].
    + destruct (eq_dec h b) as [H3 | H3].
      * rewrite H3 in H2. rewrite H2 in H1. contradiction.
      * reflexivity.
    + destruct (eq_dec h b) as [H3 | H3].
      * rewrite H3. simpl. destruct (eq_dec b b) as [H4 | H4]; try contradiction. rewrite IH. reflexivity.
      * simpl. destruct (eq_dec h b) as [H4 | H4]; try contradiction. rewrite IH. reflexivity.
Qed.

Lemma In_remove_one : forall {A : Type} eq_dec (a b : A) l,
  List.In a l -> a <> b -> List.In a (remove_one eq_dec b l).
Proof.
  intros A eq_dec a b l H1 H2. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct (eq_dec h b) as [H3 | H3].
    + destruct H1 as [H1 | H1].
      * rewrite H1 in H3. contradiction.
      * auto.
    + destruct H1 as [H1 | H1].
      * rewrite H1. left. reflexivity.
      * right. apply IH; auto.
Qed.

Lemma In_remove_one_In_l : forall {A : Type} eq_dec (a b : A) l,
  List.In a (remove_one eq_dec b l) -> List.In a l.
Proof.
  intros A eq_dec a b l H1. induction l as [| h t IH].
  - simpl in H1. contradiction.
  - simpl in H1. destruct (eq_dec h b) as [H2 | H2].
    + right; auto.
    + destruct H1 as [H1 | H1].
      * left. auto.
      * right. apply IH; auto.
Qed.

Lemma count_occ_eq_len : forall (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 : list A),
  (forall x, count_occ eq_dec l1 x = count_occ eq_dec l2 x) -> length l1 = length l2.
Proof.
  intros A eq_dec l1 l2. revert l2. induction l1 as [| h1 t1 IH].
  - intros l2 H1. simpl. destruct l2; auto. specialize (H1 a). simpl in H1. destruct (eq_dec a a); auto. lia. contradiction.
  - intros l2 H1. destruct l2 as [| h2 t2].
    + specialize (H1 h1). simpl in H1. destruct (eq_dec h1 h1); auto. lia. contradiction.
    + simpl. f_equal. destruct (eq_dec h1 h2) as [H2 | H2].
      * apply IH. intros x. specialize (H1 x). assert (h1 = x \/ h1 <> x) as [H3 | H3] by apply classic.
        -- subst. rewrite count_occ_cons_eq in H1; rewrite count_occ_cons_eq in H1; auto.
        -- rewrite count_occ_cons_neq in H1; rewrite count_occ_cons_neq in H1; auto. rewrite <- H2. auto.
      * assert (length t2 = 0 \/ length t2 > 0) as [H3 | H3] by lia. 
        -- rewrite length_zero_iff_nil in H3. subst. specialize (H1 h1). simpl in H1. destruct (eq_dec h1 h1); 
            destruct (eq_dec h2 h1); try contradiction; try lia. exfalso. apply H2. auto.
        -- specialize (IH (h2 :: (remove_one eq_dec h1 t2))). replace (length (h2 :: remove_one eq_dec h1 t2))
           with (length t2) in IH. apply IH. intros x. destruct (eq_dec h2 x) as [H4 | H4].
           ++ rewrite count_occ_cons_eq; auto. rewrite count_occ_remove_one_not_eq. specialize (H1 x).
              rewrite <- H4 in H1. rewrite count_occ_cons_neq in H1; auto. rewrite count_occ_cons_eq in H1; auto.
              rewrite <- H4. auto. intros H5. apply H2. rewrite H4, H5. auto.
           ++ destruct (eq_dec h1 x) as [H5 | H5].
              ** rewrite count_occ_cons_neq; auto. specialize (H1 x). rewrite <- H5 in H1. rewrite count_occ_cons_eq in H1; auto.
                 rewrite count_occ_cons_neq in H1; auto. rewrite H5. rewrite remove_one_In. rewrite <- H5. lia.
                 rewrite <- H5. rewrite (count_occ_In eq_dec). lia.
              ** rewrite count_occ_cons_neq; auto. rewrite count_occ_remove_one_not_eq; auto. specialize (H1 x).
                 rewrite count_occ_cons_neq in H1; auto. rewrite count_occ_cons_neq in H1; auto.
           ++ simpl. rewrite remove_one_In_length. lia. specialize (H1 h1). rewrite count_occ_cons_eq in H1; auto.
              rewrite count_occ_cons_neq in H1; auto. rewrite (count_occ_In eq_dec). lia.
Qed.

Section section_13_8.
  Variable A : Type.
  Hypothesis A_eq_dec : forall x y : option A, sumbool (x = y) (x <> y).

  Lemma lemma_13_8 : forall (l1 l2 : list (option A)),
    (length l1 < length l2)%nat -> (forall x : option A, x <> None -> count_occ A_eq_dec l1 x = count_occ A_eq_dec l2 x) -> List.In None l2.
  Proof.
    intros l1 l2 H1 H2. destruct l2 as [| h2 t2].
    - simpl in H1. lia.
    - pose proof (classic (h2 = None)) as [H3 | H3]. left. auto.
      right. pose proof (classic (List.In None t2)) as [H4 | H4]; auto. exfalso. pose proof (remove_In A_eq_dec l1 None) as H5.
      assert (~List.In None (h2 :: t2)) as H6. { intros [H6 | H6]; auto. }
      assert (forall x : option A, count_occ A_eq_dec (remove A_eq_dec None l1) x = count_occ A_eq_dec (h2 :: t2) x) as H7.
      {
        intros x. destruct (A_eq_dec x None) as [H8 | H8]; subst.
        - replace (count_occ A_eq_dec (remove A_eq_dec None l1) None) with 0. 2 : { apply eq_sym. apply count_occ_not_In; auto. }
          replace (count_occ A_eq_dec (h2 :: t2) None) with 0. 2 : { apply eq_sym. apply count_occ_not_In; auto. } lia.
        - specialize (H2 x H8). rewrite count_occ_remove_neq; auto.
      }
      assert (H8 : length (remove A_eq_dec None l1) = length (h2 :: t2)). { apply count_occ_eq_len with (eq_dec := A_eq_dec); auto. }
      pose proof (remove_length_le A_eq_dec l1 None) as H9. lia.
Qed.

End section_13_8.