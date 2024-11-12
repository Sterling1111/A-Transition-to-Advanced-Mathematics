Require Import Imports Reals_util Completeness.

Open Scope R_scope.

Notation "| x |" := (Rabs x) 
  (at level 20, x at level 99, format "| x |", no associativity) : R_scope.

Definition sequence := nat -> R.

Definition decreasing (a : sequence) : Prop :=
  forall n : nat, a n >= a (S n).

Definition increasing (a : sequence) : Prop :=
  forall n : nat, a n <= a (S n).

Definition bounded_below (a : sequence) : Prop :=
  exists LB : R, forall n : nat, LB <= a n.

Definition bounded_above (a : sequence) : Prop := 
  exists UB : R, forall n : nat, UB >= a n.

Definition eventually_decreasing (a : sequence) : Prop :=
  exists (N : nat),
    forall (n : nat), (n >= N)%nat -> a n >= a (S n).

Definition eventually_increasing (a : sequence) : Prop :=
  exists (N : nat),
    forall (n : nat), (n >= N)%nat -> a n <= a (S n).

Definition arithmetic_sequence (a : sequence) (c d : R) : Prop :=
  a = (fun n => c + d * INR n).

Definition geometric_sequence (a : sequence) (c r : R) : Prop :=
  a = (fun n => c * r ^ n).

Definition limit_of_sequence (a : sequence) (L : R) : Prop :=
  forall ε : R, ε > 0 ->
    exists N : R, forall n : nat, INR n > N -> |a n - L| < ε.

Definition convergent_sequence (a : sequence) : Prop :=
  exists (L : R), limit_of_sequence a L.

Definition divergent_sequence (a : sequence) : Prop :=
  ~ convergent_sequence a.

Definition lower_bound (a : sequence) (LB : R) : Prop :=
  forall n : nat, LB <= a n.

Definition upper_bound (a : sequence) (UB : R) : Prop :=
  forall n : nat, UB >= a n.

Definition a_bounded_above_by_b (a b : sequence) : Prop :=
  forall n : nat, a n <= b n.

Definition a_bounded_below_by_b (a b : sequence) : Prop :=
  forall n : nat, a n >= b n.

Definition a_eventually_bounded_above_by_b (a b : sequence) : Prop :=
  exists (N : R), forall n : nat, INR n > N -> a n <= b n.

Definition a_eventually_bounded_below_by_b (a b : sequence) : Prop :=
  exists (N : R), forall n : nat, INR n > N -> a n >= b n.

Lemma Rinv_lt_0 : forall r, 
  / r < 0 -> r < 0.
Proof.
  intros r H1. pose proof (Rtotal_order r 0) as [H2 | [H2 | H2]]; try lra.
  - rewrite H2 in H1. rewrite Rinv_0 in H1. lra.
  - apply Rinv_0_lt_compat in H2. lra.  
Qed.

Lemma Rinv_gt_0 : forall r,
  / r > 0 -> r > 0.
Proof.
  intros r H1. pose proof (Rtotal_order r 0) as [H2 | [H2 | H2]]; try lra.
  - apply Rinv_0_lt_compat in H1. rewrite Rinv_inv in H1. lra.
  - rewrite H2 in H1. rewrite Rinv_0 in H1. lra.
Qed.

Theorem theorem_34_12 : limit_of_sequence (fun n => 1 / INR n) 0.
Proof.
  intros ε H1. exists (/ ε). intros n H2. assert (/ ε > 0) as H3 by (apply Rinv_pos; auto).
  rewrite Rminus_0_r. unfold Rabs. destruct (Rcase_abs (1 / INR n)) as [H4 | H4].
  - assert (H5 : / - INR n > 0). { apply Rinv_pos. rewrite Rdiv_1_l in H4. apply Rinv_lt_0 in H4. lra. }
    assert (H6 : INR n <> 0). { assert (INR n > 0). { rewrite Rdiv_1_l in H4. apply Rinv_lt_0 in H4. lra. } lra. }
    apply Rmult_gt_compat_r with (r := ε) in H2; try lra.
    apply Rmult_gt_compat_r with (r := / - INR n) in H2; try lra.
    rewrite Rinv_opp in H2. field_simplify in H2; nra.
  - assert (H5 : / INR n > 0). { apply Rinv_pos. rewrite Rdiv_1_l in H4. nra. }
    assert (H6 : INR n <> 0). { nra. }
    apply Rmult_gt_compat_r with (r := ε) in H2; try lra.
    apply Rmult_gt_compat_r with (r := / INR n) in H2; try lra.
    field_simplify in H2; try nra. 
Qed.

Proposition proposition_34_13 : limit_of_sequence (fun n => 1 - 3 / INR n) 1.
Proof.
  intros ε H1. exists (3 / ε). intros n H2.
  replace (1 - 3 / INR n - 1) with (- 3 / INR n) by lra.
  assert (H3 : 3 / ε > 0) by (apply Rdiv_lt_0_compat; lra).
  assert (H4 : INR n > 0) by nra. assert (H5 : -3 / INR n < 0).
  { apply Rdiv_neg_pos; nra. } 
  unfold Rabs. destruct (Rcase_abs (- 3 / INR n)) as [H6 | H6]; try nra.
  field_simplify; try lra.
  apply Rmult_gt_compat_r with (r := ε) in H2; try lra.
  apply Rmult_gt_compat_r with (r := / 3 * / INR n) in H2; try lra.
  field_simplify in H2; try lra.
Qed.

Lemma Odd_not_even : forall n, Nat.Odd n -> Nat.even n = false.
Proof.
  intros n [k H1]. rewrite H1. apply Nat.even_odd.
Qed.

Proposition proposition_34_15 : limit_of_sequence (fun n => if Nat.even n then 0 else 1 / INR n) 0.
Proof.
  intros ε H1. pose proof theorem_34_12 ε H1 as [N H2]. exists N. intros n H3.
  pose proof Nat.Even_or_Odd n as [H4 | H4].
  - apply Nat.even_spec in H4. rewrite H4. rewrite Rminus_0_r. rewrite Rabs_R0. lra.
  - apply Odd_not_even in H4. rewrite H4. auto.
Qed.

Proposition proposition_34_16 : divergent_sequence (fun n => (-1) ^ n).
Proof.
  intros [L H1]. specialize (H1 (1/2) ltac:(lra)) as [N H1].
  pose proof INR_unbounded N as [n H2]. assert (0 <= INR n) as H3.
  { replace 0 with (INR 0) by auto. apply le_INR. lia. }
  assert (L >= 0 \/ L < 0) as [H4 | H4] by lra.
  - specialize (H1 (S (2 * n)) ltac:(solve_INR)). rewrite pow_1_odd in H1.
    apply Rabs_def2 in H1 as [_ H1]. lra.
  - specialize (H1 (2 * n)%nat ltac:(solve_INR)). rewrite pow_1_even in H1.
    apply Rabs_def2 in H1 as [H1 _]. lra.
Qed.

Lemma Rmax_Rgt : forall x y z, z > Rmax x y -> z > x /\ z > y.
Proof.
  intros x y z H1. unfold Rmax in H1. destruct (Rle_dec x y); lra.
Qed.

Proposition Proposition_34_19 : limit_of_sequence (fun n => INR (n + 3) / INR (2 * n - 21)) (1/2).
Proof.
  intros ε H1. set (N := Rmax (21/2) ((27 + 42 * ε) / (4 * ε))). exists N.
  intros n H2. apply Rmax_Rgt in H2 as [H2 H3].
  assert (INR (n + 3) / INR (2 * n - 21) - 1/2 = 27 / INR (4 * n - 42)) as H4.
  { solve_INR; assert (n > 10)%nat by (apply INR_lt; simpl; lra); try lia. } rewrite H4.
  assert (INR (4 * n - 42) > 0) as H5 by (solve_INR; assert (n > 10)%nat by (apply INR_lt; simpl; lra); try lia).
  unfold Rabs. destruct (Rcase_abs (27 / INR (4 * n - 42))) as [H6 | H6].
  - pose proof Rdiv_pos_pos 27 (INR (4 * n - 42)) ltac:(lra) as H7. nra.
  - assert (INR (4 * n - 42) > 27 / ε) as H7.
    {
       solve_INR. rewrite Rplus_0_l. field_simplify; try lra. apply Rmult_gt_compat_r with (r := 4) in H3; try lra.
       field_simplify in H3; try lra. replace ((42 * ε + 27) / ε) with (27 / ε + 42) in H3 by (field; lra); lra.
       assert (n > 10)%nat by (apply INR_lt; simpl; lra); try lia.
    }
    apply Rmult_gt_compat_r with (r := ε) in H7; try lra.
    apply Rmult_gt_compat_r with (r := /INR (4 * n - 42)) in H7; try lra. field_simplify in H7; try lra. apply Rinv_pos; lra.
Qed.

Lemma increasing_ge : forall (a : sequence) (n1 n2 : nat),
  increasing a -> (n1 >= n2)%nat -> a n1 >= a n2.
Proof.
  intros a n1 n2 H1 H2. unfold increasing in H1.
  induction H2.
  - lra.
  - assert (H3 : a (S m) >= a m).
    { apply Rle_ge. apply H1. }
    lra.
Qed.

Lemma decreasing_le : forall (a : sequence) (n1 n2 : nat),
  decreasing a -> (n1 >= n2)%nat -> a n1 <= a n2.
Proof.
  intros a n1 n2 H1 H2. unfold decreasing in H1.
  induction H2.
  - lra.
  - assert (H3 : a (S m) <= a m).
    { apply Rge_le. apply H1. }
    lra.
Qed.

Lemma eventually_decreasing_le : forall (a : sequence),
  eventually_decreasing a ->
    exists (N : nat),
       forall (n1 n2 : nat), (n2 >= N)%nat -> (n1 >= n2)%nat -> a n1 <= a n2.
Proof.
  intros a [N H1]. unfold eventually_decreasing in H1.
  exists N. intros n1 n2 H2. intros H3.
  induction H3.
  - lra.
  - assert (H4 : a (S m) <= a m).
    { apply Rge_le. apply H1. lia. }
    lra.
Qed.

Lemma eventually_increasing_ge : forall (a : sequence),
  eventually_increasing a ->
    exists (N : nat),
       forall (n1 n2 : nat), (n2 >= N)%nat -> (n1 >= n2)%nat -> a n1 >= a n2.
Proof.
  intros a [N H1]. unfold eventually_increasing in H1.
  exists N. intros n1 n2 H2. intros H3.
  induction H3.
  - lra.
  - assert (H4 : a (S m) >= a m).
    { apply Rle_ge. apply H1. lia. }
    lra.
Qed.

(*
  Monotonic Sequence Theorem (Increasing)

  Suppose that a is an increasing sequence and that it is bounded above. 
  Then by the completeness axiom, a has a least upper bound L. Given e > 0, 
  L - e is not an upper bound for a, so there exists a natural number N such
  that a_N > L - e. But the sequence is increasing so a_n >= a_N forall n >= N.
  So forall n >= N, a_n > L - e. Now 0 <= L - a_n < e which means that 
  |L - a_n| < e. and so lim a -> L.
*)

Lemma Monotonic_Sequence_Theorem_Increasing : forall (a : sequence),
  increasing a -> bounded_above a -> convergent_sequence a.
Proof.
  intros a H1 H2. unfold bounded_above in H2. destruct H2 as [UB H2].
  assert (H3 : is_upper_bound (fun x => exists n, a n = x) UB).
  { unfold is_upper_bound. intros x [n H3]. rewrite <- H3. apply Rge_le. apply H2. }
  assert (H4 : bound (fun x => exists n : nat, a n = x)).
  { unfold bound. exists UB. apply H3. }
  assert (H5 : {L : R | is_lub (fun x => exists n : nat, a n = x) L}).
  { apply completeness. apply H4. exists (a 0%nat). exists 0%nat. reflexivity. }
  destruct H5 as [L H5]. unfold is_lub in H5. destruct H5 as [H5 H6]. unfold is_upper_bound in H5.
  unfold convergent_sequence. exists L. intros eps H7.

  assert (H8 : ~ (is_upper_bound (fun x => exists n, a n = x) (L - eps))).
  { unfold not. intros contra. specialize (H6 (L - eps)). apply H6 in contra. lra. }
  unfold is_upper_bound in H8. unfold not in H8.

  assert (H9 : exists N : nat, a N > L - eps).
  { 
    apply not_all_not_ex. unfold not. intro H9. apply H8. intros x H10. 
    destruct H10 as [n H10]. rewrite <- H10. specialize (H9 n). 
    apply Rnot_gt_le. unfold not. apply H9.
  }
  destruct H9 as [N H9].

  assert (H10 : forall n : nat, (n >= N)%nat -> a n > L - eps).
  { intros n H. assert (a n >= a N). apply increasing_ge. apply H1. lia. lra. }
  assert (H11 : forall n : nat, (n >= N)%nat -> a n <= L).
  {  intros n H11. specialize (H5 (a n)). apply H5. exists n. reflexivity. }
  assert (H12 : forall n : nat, (n >= N)%nat -> 0 <= L - a n < eps).
  { intros n. split. 
    assert (H12 : (a n <= L) -> 0 <= L - a n). lra. apply H12. apply H11. apply H. 
    assert (H12 : (a n > L - eps) -> L - a n < eps). lra. apply H12. apply H10. apply H. }
    exists (INR N). intros n H13. specialize (H12 n). unfold Rabs. destruct Rcase_abs.
    - replace (- (a n - L)) with (L - a n) by lra. apply H12. apply Rgt_lt in H13. apply INR_lt in H13. lia.
    - assert (H14 : a n >= L) by lra. assert (H15 : a n <= L). { apply H11. apply Rgt_lt in H13. apply INR_lt in H13. lia. } 
      lra.
Qed.

Lemma Monotonic_Sequence_Theorem_Decreasing : forall (a : sequence),
  decreasing a -> bounded_below a -> convergent_sequence a.
Proof.
  intros a Hdec Hbounded.
  unfold bounded_below in Hbounded.
  destruct Hbounded as [LB HLB].

  assert (H3 : is_lower_bound (fun x => exists n, a n = x) LB).
  { unfold is_lower_bound. intros x [n H3]. rewrite <- H3. apply Rle_ge. apply HLB. }

  assert (H4 : has_lower_bound (fun x => exists n : nat, a n = x)).
  { unfold has_lower_bound. exists LB. apply H3. }

  assert (H5 : {L : R | is_glb (fun x => exists n : nat, a n = x) L}).
  { apply completeness_lower_bound. apply H4. exists (a 0%nat). exists 0%nat. reflexivity. }

  destruct H5 as [L H5]. unfold is_glb in H5. destruct H5 as [H5 H6]. unfold is_lower_bound in H5.

  unfold convergent_sequence. exists L. intros eps H7.

  assert (H8 : ~ (is_lower_bound (fun x => exists n, a n = x) (L + eps))).
  { unfold not. intros contra. specialize (H6 (L + eps)). apply H6 in contra. lra. }

  unfold is_lower_bound in H8. unfold not in H8.

  assert (H9 : exists N : nat, a N < L + eps).
  { 
    apply not_all_not_ex. unfold not. intro H9. apply H8. intros x H10. 
    destruct H10 as [n H10]. rewrite <- H10. specialize (H9 n). 
    apply Rnot_lt_ge. unfold not. apply H9.
  }
  destruct H9 as [N H9].

  assert (H10 : forall n : nat, (n >= N)%nat -> a n < L + eps).
  { intros n H. assert (a n <= a N). apply decreasing_le. apply Hdec. lia. lra. }

  assert (H11 : forall n : nat, (n >= N)%nat -> a n >= L).
  {  intros n H11. specialize (H5 (a n)). apply H5. exists n. reflexivity. }

  assert (H12 : forall n : nat, (n >= N)%nat -> 0 <= a n - L < eps).
  { intros n. split. 
    assert (H12 : (a n >= L) -> 0 <= a n - L). lra. apply H12. apply H11. apply H. 
    assert (H12 : (a n < L + eps) -> a n - L < eps). lra. apply H12. apply H10. apply H. }
    
  exists (INR N). intros n H13. specialize (H12 n). unfold R_dist.
  unfold Rabs. destruct Rcase_abs.
  - replace (- (a n - L)) with (L - a n) by lra. assert (H14 : a n >= L).
    { apply H11. apply Rgt_lt in H13. apply INR_lt in H13. lia. } lra.
  - apply H12. apply Rgt_lt in H13. apply INR_lt in H13. lia.
Qed.

(*
  Monotonic Sequence Theorem (Eventually Increasing)

  Suppose that a is an eventually increasing sequence that is bound above.
  Construct a set S of all the elements of a starting from the point of
  continual increase. Then this set has a least upper bound since it is bound
  above by at most the bound of sequence a. Then the proof follows the same
  as above.
*)

Lemma Monotonic_Sequence_Theorem_Increasing_Eventually : forall (a : sequence),
  eventually_increasing a -> bounded_above a -> convergent_sequence a.
Proof.
  intros a [N H1] [UB H2].
  pose (b := (fun n => a ((n + N)%nat)) : sequence).

  assert (H3 : increasing b) by (intros n; apply H1; lia).
  assert (H4 : bounded_above b) by (exists UB; intros n; apply H2).

  assert (H5 : convergent_sequence b).
  { apply Monotonic_Sequence_Theorem_Increasing. apply H3. apply H4. }

  destruct H5 as [L H5].
  exists L. intros eps.
  specialize (H5 eps).
  intros H6.
  destruct H5 as [N' H5]; auto.
  exists (INR N + Rmax N' 0). intros n H7.
  specialize (H5 (n - N)%nat).
  unfold b in H5. assert (N' < 0 \/ N' >= 0) as [H8 | H8] by lra.
  - replace (Rmax N' 0) with 0 in H7. 2 : { rewrite Rmax_right; lra. } rewrite Rplus_0_r in H7.
    apply INR_lt in H7. replace (n - N + N)%nat with n in H5 by lia. apply H5. pose proof pos_INR (n - N) as H9. lra.
  - assert (Rmax N' 0 >= 0) as H9. { rewrite Rmax_left; lra. } assert (INR n > INR N) as H10 by lra.
    apply INR_lt in H10. replace (n - N + N)%nat with n in H5 by lia. apply H5.
    assert (Rmax N' 0 = N') as H11. { unfold Rmax. destruct (Rle_dec N'); lra. } solve_INR. apply INR_lt in H10. lia.
Qed.

Lemma Monotonic_Sequence_Theorem_Decreasing_Eventually : forall (a : sequence),
  eventually_decreasing a -> bounded_below a -> convergent_sequence a.
Proof.
  intros a [N H1] [LB H2].
  pose (b := (fun n => a ((n + N)%nat)) : sequence).

  assert (H : convergent_sequence b).
  { apply Monotonic_Sequence_Theorem_Decreasing; 
    [intros n; apply H1; lia | exists LB; intros n; apply H2]. }

  destruct H as [L H]. exists L.
  intros eps H6. destruct (H eps H6) as [N' H5].
  exists (INR N + Rmax N' 0). intros n H7.
  specialize (H5 (n - N)%nat). unfold b in H5. assert (N' < 0 \/ N' >= 0) as [H8 | H8] by lra.
  - replace (Rmax N' 0) with 0 in H7. 2 : { rewrite Rmax_right; lra. } rewrite Rplus_0_r in H7.
    apply INR_lt in H7. replace (n - N + N)%nat with n in H5 by lia. apply H5. pose proof pos_INR (n - N) as H9. lra.
  - assert (Rmax N' 0 >= 0) as H9. { rewrite Rmax_left; lra. } assert (INR n > INR N) as H10 by lra.
    apply INR_lt in H10. replace (n - N + N)%nat with n in H5 by lia. apply H5.
    assert (Rmax N' 0 = N') as H11. { unfold Rmax. destruct (Rle_dec N'); lra. } solve_INR. apply INR_lt in H10. lia.
Qed.

Theorem Monotonic_Sequence_Theorem : forall (a : sequence),
  (increasing a /\ bounded_above a) \/ (decreasing a /\ bounded_below a) -> convergent_sequence a.
Proof.
  intros a [[H1 H2] | [H1 H2]]; 
  [apply Monotonic_Sequence_Theorem_Increasing | apply Monotonic_Sequence_Theorem_Decreasing]; auto.
Qed.

Theorem Monotonic_Sequence_Theorem_Strong : forall (a : sequence),
  (eventually_increasing a /\ bounded_above a) \/ (eventually_decreasing a /\ bounded_below a) -> convergent_sequence a.
Proof.
  intros a [[H1 H2] | [H1 H2]]; 
  [apply Monotonic_Sequence_Theorem_Increasing_Eventually | apply Monotonic_Sequence_Theorem_Decreasing_Eventually]; auto.
Qed.

Lemma sequence_squeeze_lower : forall a b LB,
  limit_of_sequence a LB -> a_eventually_bounded_below_by_b a b -> lower_bound b LB -> limit_of_sequence b LB.
Proof.
  intros a b LB H1 [N1 H2] H3 ε H4. specialize (H1 ε H4) as [N2 H1]. exists (Rmax N1 N2). intros n H5.
  specialize (H1 n ltac:(apply Rmax_Rgt in H5; lra)). specialize (H2 n ltac:(apply Rmax_Rgt in H5; lra)).
  specialize (H3 n). assert (|b n - LB| <= |a n - LB|) as H6 by solve_abs. lra.
Qed.

Lemma sequence_squeeze_upper : forall a b UB,
  limit_of_sequence a UB -> a_eventually_bounded_above_by_b a b -> upper_bound b UB -> limit_of_sequence b UB.
Proof.
  intros a b UB H1 [N1 H2] H3 ε H4. specialize (H1 ε H4) as [N2 H1]. exists (Rmax N1 N2). intros n H5.
  specialize (H1 n ltac:(apply Rmax_Rgt in H5; lra)). specialize (H2 n ltac:(apply Rmax_Rgt in H5; lra)).
  specialize (H3 n). assert (|b n - UB| <= |a n - UB|) as H6 by solve_abs. lra.
Qed.

Lemma sequence_squeeze : forall a b c L,
  limit_of_sequence a L -> limit_of_sequence c L -> a_eventually_bounded_below_by_b b a -> a_eventually_bounded_above_by_b b c -> limit_of_sequence b L.
Proof.
  intros a b c L H1 H2 [N3 H3] [N4 H4] ε H5. specialize (H1 ε H5) as [N1 H1]. specialize (H2 ε H5) as [N2 H2].
  set (N := Rmax (Rmax N1 N2) (Rmax N3 N4)). assert (N >= N1 /\ N >= N2 /\ N >= N3 /\ N >= N4) as [H6 [H7 [H8 H9]]] by (unfold N; solve_max).
  exists N. intros n H10. specialize (H1 n ltac:(lra)). specialize (H2 n ltac:(lra)). specialize (H3 n ltac:(lra)). specialize (H4 n ltac:(lra)).
  solve_abs.
Qed.

Lemma limit_of_const_sequence : forall c,
  limit_of_sequence (fun _ => c) c.
Proof.
  intros; exists 0; solve_abs.
Qed.

Lemma limit_of_sequence_add : forall a b L1 L2,
  limit_of_sequence a L1 -> limit_of_sequence b L2 -> limit_of_sequence (fun n => a n + b n) (L1 + L2).
Proof.
  intros a b L1 L2 H1 H2 ε H3. specialize (H1 (ε/2) ltac:(lra)) as [N1 H1]. specialize (H2 (ε/2) ltac:(lra)) as [N2 H2].
  exists (Rmax N1 N2). intros n H4. specialize (H1 n ltac:(apply Rmax_Rgt in H4; lra)). specialize (H2 n ltac:(apply Rmax_Rgt in H4; lra)).
  solve_abs.
Qed.

Lemma limit_of_sequence_sub : forall a b L1 L2,
  limit_of_sequence a L1 -> limit_of_sequence b L2 -> limit_of_sequence (fun n => a n - b n) (L1 - L2).
Proof.
  intros a b L1 L2 H1 H2 ε H3. specialize (H1 (ε/2) ltac:(lra)) as [N1 H1]. specialize (H2 (ε/2) ltac:(lra)) as [N2 H2].
  exists (Rmax N1 N2). intros n H4. specialize (H1 n ltac:(apply Rmax_Rgt in H4; lra)). specialize (H2 n ltac:(apply Rmax_Rgt in H4; lra)).
  solve_abs.
Qed.

Lemma limit_of_sequence_mul_const : forall a c L,
  limit_of_sequence a L -> limit_of_sequence (fun n => c * a n) (c * L).
Proof.
  intros a c L H1 ε H2. assert (c = 0 \/ c <> 0) as [H3 | H3] by lra.
  - exists 0. solve_abs.
  - specialize (H1 (ε / Rabs c) ltac:(apply Rdiv_pos_pos; solve_abs)) as [N H1].
    exists N. intros n H4. specialize (H1 n ltac:(apply H4)).
    apply Rmult_lt_compat_r with (r := Rabs c) in H1; field_simplify in H1; solve_abs.
Qed.