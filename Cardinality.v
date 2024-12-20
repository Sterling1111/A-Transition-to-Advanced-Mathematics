Require Import Imports Sets Functions Chapter6 Notations Sums WI_SI_WO.
Import SetNotations.

Notation subType := SetNotations.subType.

Open Scope R_scope.

Definition n_N (n : nat) : Type := subType (fun x : nat => exists k : nat, (x = n * k)%nat).

Notation "n 'N'" := (n_N n) (at level 0, format "n 'N'").

Open Scope Z_scope.

Theorem theorem_29_4 : ‖ ℕ ‖ = ‖ ℤ ‖.
Proof.
  apply eq_cardinality_Type.
  set (f := fun n : nat => if Nat.even n then Z.of_nat (n / 2) else - Z.of_nat (n / 2 + 1)). left. split.
  exists f. split.
  - intros x y H1. unfold f in H1. destruct (Nat.even x) eqn:H2, (Nat.even y) eqn:H3.
    -- apply Nat.even_spec in H2 as [j H2], H3 as [k H3]; subst. apply Nat2Z.inj in H1.
       do 2 (rewrite Nat.mul_comm, Nat.div_mul in H1; try lia).
    -- pose proof Zle_0_nat (x / 2) as H4. pose proof Zle_0_nat (y / 2 + 1) as H5. lia.
    -- pose proof Zle_0_nat (x / 2 + 1) as H4. pose proof Zle_0_nat (y / 2) as H5. lia.
    -- apply Z.opp_inj in H1. apply Nat_even_false_Odd in H2 as [j H2], H3 as [k H3]; subst.
       apply Nat2Z.inj in H1. rewrite Nat.mul_comm in H1. rewrite Nat.mul_comm with (n := 2%nat) in H1.
       rewrite Nat.div_add_l in H1; try lia. rewrite Nat.div_add_l in H1; try lia.
  - intros y. assert (y >= 0 \/ y < 0) as [H1 | H1] by lia.
    -- exists (2 * Z.to_nat y)%nat. unfold f. destruct (Nat.even (2 * Z.to_nat y)) eqn:H2.
       * rewrite Nat.mul_comm. rewrite Nat.div_mul; try lia.
       * apply Nat_even_false_Odd in H2 as [j H2]. lia.
    -- exists (2 * Z.to_nat (- y) - 1)%nat. unfold f. destruct (Nat.even (2 * Z.to_nat (- y) + 1)) eqn:H2.
       * apply Nat.even_spec in H2 as [j H2]. lia.
       * destruct (Nat.even (2 * Z.to_nat (- y) - 1)) eqn:H3.
         + apply Nat.even_spec in H3 as [j H3]. lia.
         + apply Nat_even_false_Odd in H3 as [j H3]. rewrite H3. rewrite Nat.mul_comm.
           rewrite Nat.div_add_l; try lia. simpl. lia.
  - exists 0%nat, 0%Z. auto.
Qed.

Lemma cardinal_eq_refl : forall (T : Type) (A : Ensemble T), ‖ A ‖ = ‖ A ‖.
Proof.
  intros T A. pose proof classic (A = ⦃⦄) as [H1 | H1]; [left | right; repeat split]; auto.
  - exists (fun x => x). split.
    -- intros x y H2. auto.
    -- intros y. exists y. auto.
Qed.

Lemma cardinal_eq_sym : forall (T1 T2 : Type) (A : Ensemble T1) (B : Ensemble T2), ‖ A ‖ = ‖ B ‖ -> ‖ B ‖ = ‖ A ‖.
Proof.
  intros T1 T2 A B [[H1 H2] | [H1 [H2 [f [H3 H4]]]]]; [left | right; repeat split]; auto.
  apply choice in H4 as [g H5]. exists g. split.
  - intros x y H6. specialize (H5 (f (g x))) as H7. rewrite H6 in H7 at 2.
    do 3 rewrite H5 in H7; auto.
  - intros y. specialize (H3 y (g (f y))). specialize (H5 (f y)) as H6.
    rewrite <- H6 in H3 at 1. exists (f y). rewrite H3; auto. rewrite H6. auto.
Qed.

Lemma cardinal_eq_trans : forall (T1 T2 T3 : Type) (A : Ensemble T1) (B : Ensemble T2) (C : Ensemble T3),
  ‖ A ‖ = ‖ B ‖ -> ‖ B ‖ = ‖ C ‖ -> ‖ A ‖ = ‖ C ‖.
Proof.
  intros T1 T2 T3 A B C [H1 | H1].
Admitted.

Definition countably_infinite {T : Type} (A : Ensemble T) : Prop := ‖ ℕ ‖ = ‖ A ‖.
Definition countable {T : Type} (A : Ensemble T) : Prop := Finite_set A \/ countably_infinite A.

Theorem theorem_29_14 : forall (T : Type) (A B : Ensemble T),
  Infinite_set B -> B ⊆ A -> countably_infinite A -> countably_infinite B.
Proof.
  intros T A B H1 H2. unfold countably_infinite. unfold Type_to_Ensemble. intros [[_ H3] | [_ [_ [f [H3 H4]]]]].
  - assert (B <> ⦃⦄) as H5. { apply not_Empty_In. apply Infinite_exists_In; auto. } exfalso. apply H5. autoset.
  - unfold countably_infinite. unfold cardinal_eq. right. repeat split.
    -- apply not_Empty_In. exists 0%nat. apply Full_intro.
    -- apply not_Empty_In. apply Infinite_exists_In; auto.
    -- unfold injective in H3. unfold surjective in H4. 
Admitted.

Open Scope Q_scope.

Definition Npos_S : Ensemble nat := fun n => (n > 0)%nat.
Definition Npos_T := subType (Npos_S).

Definition Q' := Full_set (ℤ * positive).
Definition Qpos : Ensemble Q := fun q => q > 0.
Definition Qpos' := Full_set (Npos_T * Npos_T).
Definition Q'' : Ensemble ℝ := fun r => exists a b : ℤ, (r = (IZR a) / IZR b)%R.
Definition Q''' : Ensemble ℚ := ℚ.

Lemma card_Q''_eq_card_Q : ‖ Q ‖ = ‖ Q' ‖.
Proof.
  unfold Type_to_Ensemble. apply cardinal_eq_sym. unfold cardinal_eq. right. repeat split.
  - apply not_Empty_In. exists (1%Z, 1%positive). apply Full_intro.
  - apply not_Empty_In. exists 1. apply Full_intro.
  - repeat rewrite subType_Full_set. set (f := fun p : ℤ * positive => let (n, d) := p in (n # d)%Q). exists f. split.
    -- intros [a b] [c d] H1. unfold f in H1. injection H1; intros H2 H3. subst. reflexivity.
    -- intros q. destruct q as [a b]. exists (a, b). unfold f. reflexivity. 
Qed.

Lemma Npos_In_Qpos : forall n d : Npos_T, (Z.of_nat (val Npos_S n) # Pos.of_nat (val Npos_S d)) ∈ Qpos.
Proof.
  intros [n H1] [d H2]. unfold Ensembles.In, Npos_S, Qpos in *. simpl. unfold Qgt. simpl. lia.
Qed.

Lemma subType_eq {A : Type} {E : Ensemble A} (x y : subType E) :
  val E x = val E y <-> x = y.
Proof.
  split.
  - intros H1. destruct x as [x H2], y as [y H3]. simpl in *. subst. f_equal. apply proof_irrelevance.
  - intros H1. subst. reflexivity.
Qed.

Lemma Qgt_0 : forall q, q > 0 -> let (n, _) := q in (n > 0)%Z.
Proof.
  intros q H1. destruct q as [n d]. unfold Qgt in H1. simpl in H1. lia.
Qed.

Open Scope nat_scope.

Lemma triangular_number_bounds : forall n,
  exists t, t * (t + 1) / 2 <= n < (t + 1) * (t + 2) / 2.
Proof.
  intros n.
  assert (n = 0 \/ n = 1 \/ n = 2 \/ n > 2) as [H1 | [H1 | [H1 | H1]]] by lia;
    [exists 0 | exists 1 | exists 1 |]; try (simpl; lia).
  set (E t := t * (t + 1) / 2 > n). assert (exists t, E t) as H2.
  { exists n. unfold E. pose proof sum_n_divisible n as [j H3]. rewrite H3. rewrite Nat.div_mul; nia. }
  pose proof WI_SI_WO as [_ [_ WO]]. apply WO in H2 as [t [H2 H3]].
  exists (t - 1). assert (t = 0 \/ t > 0) as [H4 | H4] by lia.
  - rewrite H4 in H2. unfold E in H2. simpl in H2. lia.
  - split.
    -- unfold E in H2. pose proof classic ((t - 1) * (t - 1 + 1) / 2 <= n) as [H5 | H5]; auto.
       apply not_le in H5. specialize (H3 (t - 1) H5); lia.
    -- replace (t - 1 + 1) with t by lia. replace (t - 1 + 2) with (t + 1) by lia. unfold E in H2. auto.
Qed.

Lemma theorem_30_3 : ‖ ℕ ‖ = ‖ ℕ × ℕ ‖.
Proof.
  apply cardinal_eq_sym. unfold cardinal_eq. right. repeat split.
  - apply not_Empty_In. unfold Ensembles.In, set_prod. exists (1, 1), 1, 1. repeat split.
  - apply not_Empty_In. exists 1. apply Full_intro.
  - replace (ℕ × ℕ) with (Full_set (ℕ * ℕ)). 
    2 : { apply set_equal_def. intros [n1 n2]. split; intros H1; try apply Full_intro. exists n1, n2. repeat split. }
    set (f := fun p : ℕ * ℕ => let (n1, n2) := p in (n1 + n2) * (n1 + n2 + 1) / 2 + n2).
    apply exists_bijection with (f := f). split.
    -- intros [m n] [p q] H1. unfold f in H1. assert (m + n < p + q \/ m + n = p + q \/ m + n > p + q) as [H2 | [H2 | H2]] by lia.
       * set (a := m + n). set (d := p + q - a). replace (m + n) with a in H1 by lia. replace (p + q) with (a + d) in H1 by lia.
         assert (H3 : n - q = (a + d) * (a + d + 1) / 2 - a * (a + 1) / 2) by lia.
         replace ((a + d) * (a + d + 1) / 2 - a * (a + 1) / 2) with (a * d + d * (d + 1) / 2) in H3.
         2 :
         { pose proof sum_n_divisible a as [j H4]. pose proof sum_n_divisible (a + d) as [k H5]. pose proof sum_n_divisible d as [i H6].
             rewrite H4, H5, H6. repeat rewrite Nat.div_mul; try lia. }
         assert (d = 0 \/ d > 0) as [H4 | H4] by lia; try lia.
         assert (d * (d + 1) / 2 >= 1) as H5. { pose proof sum_n_divisible d as [j H5]. rewrite H5. rewrite Nat.div_mul; lia. }
         assert (a * d + d * (d + 1) / 2 >= a + 1) as H6 by nia. assert (n > a + q) as H7 by lia. unfold a in H7. lia.
       * rewrite H2 in H1. f_equal; lia.
       * set (a := p + q). set (d := m + n - a). replace (p + q) with a in H1 by lia. replace (m + n) with (a + d) in H1 by lia.
         assert (H3 : q - n = (a + d) * (a + d + 1) / 2 - a * (a + 1) / 2) by lia.
         replace ((a + d) * (a + d + 1) / 2 - a * (a + 1) / 2) with (a * d + d * (d + 1) / 2) in H3.
         2 :
         { pose proof sum_n_divisible a as [j H4]. pose proof sum_n_divisible (a + d) as [k H5]. pose proof sum_n_divisible d as [i H6].
             rewrite H4, H5, H6. repeat rewrite Nat.div_mul; try lia. }
         assert (d = 0 \/ d > 0) as [H4 | H4] by lia; try lia.
         assert (d * (d + 1) / 2 >= 1) as H5. { pose proof sum_n_divisible d as [j H5]. rewrite H5. rewrite Nat.div_mul; lia. }
         assert (a * d + d * (d + 1) / 2 >= a + 1) as H6 by nia. assert (n > a + m) as H7 by lia. unfold a in H7. lia.
    -- intros n. pose proof triangular_number_bounds n as [t [H1 H2]]. set (b := n - t * (t + 1) / 2). set (a := t - b). exists (a, b). unfold f.
       unfold a, b. assert (n >= t \/ n < t) as [H3 | H3]; assert (t * (t + 1) / 2 = n \/ t * (t + 1) / 2 < n) as [H4 | H4]; try lia.
       * rewrite H4. replace (n - n) with 0 by lia. rewrite Nat.sub_0_r. repeat rewrite Nat.add_0_r. lia.
       * assert (t >= (n - t * (t + 1) / 2) \/ t < (n - t * (t + 1) / 2)) as [H5 | H5] by lia.
         ** replace ((t - (n - t * (t + 1) / 2) + (n - t * (t + 1) / 2))) with t by nia. lia.
         ** replace (t + 2) with (t + 1 + 1) in H2 by lia. pose proof sum_n_divisible (t+1) as [j H6].
            pose proof (sum_n_divisible t) as [k H7]. rewrite H6 in H2. rewrite H7 in H5. rewrite Nat.div_mul in H2; try lia.
            rewrite Nat.div_mul in H5; lia.
       * rewrite H4. replace (n - n) with 0 by lia. rewrite Nat.sub_0_r. repeat rewrite Nat.add_0_r. auto.
       * replace ((t - (n - t * (t + 1) / 2) + (n - t * (t + 1) / 2))) with t by nia. lia.
Qed.

Theorem theorem_30_3' : forall {T : Type} (A B : Ensemble T),
  countably_infinite A -> countably_infinite B -> countably_infinite (A × B).
Proof.
  intros T A B H1 H2. unfold countably_infinite in *.

  
   unfold Type_to_Ensemble in *. unfold cardinal_eq in *.
  right. assert (H3 : Full_set ℕ ≠ ⦃⦄). { apply not_Empty_In. exists 0%nat. apply Full_intro. }
  repeat split; auto.
  - destruct H1 as [[H1 _] | [H1 [H4 H5]]]; destruct H2 as [[H2 _] | [H2 [H6 H7]]]; auto.
    apply not_Empty_In. apply not_Empty_In in H4 as [a H4]. apply not_Empty_In in H6 as [b H6].
    exists (a, b). exists a, b. auto.
  - destruct H1 as [[H1 _] | [H1 [H4 H5]]]; destruct H2 as [[H2 _] | [H2 [H6 H7]]]; try tauto.
    destruct H5 as [f H5]. destruct H7 as [g H7]. pose proof theorem_30_3 as [H8 | [_ [_ [h H9]]]]; try tauto.
    unfold Type_to_Ensemble in h. assert (H10 : forall a b : T, a ∈ A -> b ∈ B -> (a, b) ∈ A × B).
    { intros a b H10 H11. unfold Ensembles.In, set_prod. exists a, b. auto. }
    set (f' := fun n : subType ℕ => let (a, Ha) := f n in let (b, Hb) := g n in mkSubType _ (A × B) (a, b) ltac:(apply H10; [ apply Ha | apply Hb] )).
    exists f'. split.
    -- intros [n1 H11] [n2 H12] H13. unfold f' in H13. destruct H5 as [H5 _]. unfold injective in H5.
Abort.

Lemma card_Nat_pos_eq_Qpos : ‖ Qpos ‖ = ‖ Qpos' ‖.
Proof.
  apply cardinal_eq_sym. unfold cardinal_eq. right. repeat split.
  - apply not_Empty_In. set (one := mkSubType ℕ (fun n => (n > 0)%nat) 1%nat ltac:(unfold Ensembles.In; auto)). simpl in *. exists (one, one). apply Full_intro.
  - apply not_Empty_In. exists 1%Q. constructor.
  - repeat rewrite subType_Full_set.
   set (f := fun p : Npos_T * Npos_T => let (n, d) := p in mkSubType Q Qpos (Z.of_nat (val Npos_S n) # Pos.of_nat (val Npos_S d))%Q ltac:(apply Npos_In_Qpos)).
   exists f. split.
   -- intros [[n1 H1] [d1 H2]] [[n2 H3] [d2 H4]] H5. unfold f in H5; simpl in H5; injection H5; clear H5 f; intros H5 H6. unfold Npos_S, Ensembles.In in *.
      apply Nat2Pos.inj in H5; apply Nat2Z.inj in H6; try lia. subst. apply f_equal2; apply subType_eq; simpl; reflexivity.
   -- intros [[n d] H1]. unfold Qpos, Ensembles.In in H1. set (n' := Z.to_nat n). set (d' := Pos.to_nat d).
      assert (n > 0)%Z as H2. { pose proof Qgt_0 (n # d) H1. auto. } assert (n' > 0)%nat as H3 by lia. assert (d' > 0)%nat as H4 by lia.
      set (n1 := mkSubType ℕ Npos_S n' H3). set (d1 := mkSubType ℕ Npos_S d' H4). exists (n1, d1). unfold f. apply subType_eq. simpl.
      replace (Z.of_nat n') with n by lia. replace (Pos.of_nat d') with d by lia. reflexivity.
Qed.

Definition nat_to_Q (n d : nat) : Q := (Z.of_nat n) # (Pos.of_nat d).
Definition Q_num_nat (q : Q) : nat := Z.to_nat (Qnum q).
Definition Q_den_nat (q : Q) : nat := Pos.to_nat (Qden q).

Definition next_Qpos (n d : nat) : nat * nat := 
  (if d =? 1 then (1, n+1) else (n+1, d-1))%nat.

Open Scope nat_scope.

Lemma next_Qpos_fst_gt_0 : forall n d, n > 0 -> d > 0 -> fst (next_Qpos n d) > 0.
Proof.
  intros n d H1 H2. unfold next_Qpos. destruct d; simpl; try lia.
  destruct d; simpl; try lia.
Qed.

Lemma next_Qpos_snd_gt_0 : forall n d, n > 0 -> d > 0 -> snd (next_Qpos n d) > 0.
Proof.
  intros n d H1 H2. unfold next_Qpos. destruct d; simpl; try lia.
  destruct d; simpl; try lia.
Qed.

Fixpoint func2 (iter n d : nat) : (nat * nat) :=
  match iter with
  | 0%nat => (n, d)
  | S iter' => func2 iter' (fst (next_Qpos n d)) (snd (next_Qpos n d))
  end.

Lemma func2_fst_gt_0 : forall n d iter, n > 0 -> d > 0 -> fst (func2 iter n d) > 0.
Proof.
  intros n d iter. generalize dependent n. generalize dependent d. induction iter as [| k IH]. 
  - simpl. lia.
  - intros d n H1 H2. simpl. specialize (IH (snd (next_Qpos n d)) (fst (next_Qpos n d)) ltac:(apply next_Qpos_fst_gt_0; auto) ltac:(apply next_Qpos_snd_gt_0; auto)).
    auto.
Qed.

Lemma func2_snd_gt_0 : forall n d iter, n > 0 -> d > 0 -> snd (func2 iter n d) > 0.
Proof.
  intros n d iter. generalize dependent n. generalize dependent d. induction iter as [| k IH]. 
  - simpl. lia.
  - intros d n H1 H2. simpl. specialize (IH (snd (next_Qpos n d)) (fst (next_Qpos n d)) ltac:(apply next_Qpos_fst_gt_0; auto) ltac:(apply next_Qpos_snd_gt_0; auto)).
    auto.
Qed.

Definition Npos_Qpos_bijection (n : Npos_T) : subType Qpos' :=
  let n' := val Npos_S n in
  let n'' := (fst (func2 n' 1 1)) in
  let d'' := (snd (func2 n' 1 1)) in
  let n''' := mkSubType ℕ Npos_S n'' ltac:(apply func2_fst_gt_0; auto) in
  let d''' := mkSubType ℕ Npos_S d'' ltac:(apply func2_snd_gt_0; auto) in
  let q := mkSubType (Npos_T * Npos_T) Qpos' (n''', d''') ltac:(constructor) in q.

Lemma card_Npos_eq_card_Qpos : ‖ Npos_S ‖ = ‖ Qpos' ‖.
Proof.
  unfold cardinal_eq. right. repeat split.
  - apply not_Empty_In. admit.
  - admit.
  - exists Npos_Qpos_bijection. split.
    -- intros [n1 H1] [n2 H2] H3. apply subType_eq. simpl. injection H3; intros H4 H5. admit.
    -- intros [[[n H1] [d H2]] H3]. unfold Ensembles.In, Npos_S in *. unfold Qpos', Ensembles.In in H1. unfold Npos_Qpos_bijection. admit.
Qed.  


Fixpoint next_Q (n d : nat) (l : list Q) : (list Q * Q) :=
  let q := nat_to_Q n d in
  match d with
  | 0%nat => (l, 0)
  | 1%nat => (l ++ [q], q)
  | S d' => match (find (fun q' => Qeq_bool q' q) l) with
            | None => (l ++ [q], q)
            | Some _ => next_Q (n + 1) d' l
            end
  end.

Fixpoint func1 (iter : nat) (n d : nat) (l : list Q) : list Q :=
  match iter with
  | 0%nat => l
  | S iter' =>
      let (l', q) := next_Q n d l in
      let d' := Q_den_nat q in
      let n' := Q_num_nat q in
      match d' with
      | 1%nat => func1 iter' 1 (n' + 1) l'
      | _ => func1 iter' (n' + 1) (d' - 1) l'
      end
  end.

Fixpoint last_element {A : Type} (l : list A) (default : A) : A :=
  match l with
  | [] => default
  | [x] => x
  | _ :: t => last_element t default
  end.

Definition N_Qpos_bijection (n : nat) : Q :=
  let l := func1 (n + 1) 1 1 [1] in
  last_element l 0.

Compute (map N_Qpos_bijection (seq 0 10)).

Theorem theorem_29_5 : ‖ ℕ ‖ = ‖ ℚ ‖.
Proof.
Admitted.