Require Import Imports Sets Notations Functions.
Import SetNotations.

Open Scope R_scope.

Definition is_lower_bound (E:Ensemble ℝ) lb := forall x, x ∈ E -> x >= lb.
Definition is_upper_bound (E:Ensemble ℝ) ub := forall x, x ∈ E -> x <= ub.

Definition has_lower_bound (E:Ensemble ℝ) := exists lb, is_lower_bound E lb.
Definition has_upper_bound (E:Ensemble ℝ) := exists ub, is_upper_bound E ub.

Definition is_glb (E:Ensemble ℝ) glb :=
  is_lower_bound E glb /\ (forall lb, is_lower_bound E lb -> glb >= lb).

Definition is_lub (E:Ensemble ℝ) lub :=
  is_upper_bound E lub /\ (forall ub, is_upper_bound E ub -> lub <= ub).

Lemma completeness_upper_bound : forall E:Ensemble ℝ,
  has_upper_bound E -> E ≠ ∅ -> { sup | is_lub E sup }.
Proof.
  intros E H1 H2. apply not_Empty_In in H2. assert (H3 : bound E).
  { destruct H1 as [ub H1]. exists ub. intros x H3. apply H1. apply H3. }
  apply completeness; auto.
Qed.

Lemma completeness_lower_bound :
    forall E:Ensemble ℝ, has_lower_bound E -> E ≠ ∅ -> { inf | is_glb E inf }.
Proof.
  intros E H1 H2. set (E' := fun x => -x ∈ E). assert (H3 : forall x, x ∈ E <-> -x ∈ E').
  {
    intros x. split; intros H3.
    - unfold In, E' in *. rewrite Ropp_involutive. apply H3.
    - unfold In, E' in *. rewrite Ropp_involutive in H3. apply H3.
  }
  assert (H4 : has_upper_bound E').
  { destruct H1 as [lb H1]. exists (-lb). intros x H4. specialize (H1 (-x) H4). lra. }
  assert (H5 : E' ≠ ∅).
  { apply not_Empty_In in H2 as [x H2]. apply not_Empty_In. exists (-x). apply H3 in H2; auto. }
  destruct (completeness_upper_bound E' H4 H5) as [lub H6]. exists (-lub). split.
  - intros x H7. destruct H6 as [H6 _]. specialize (H6 (-x)). apply H3 in H7. specialize (H6 H7). lra.
  - intros lb H7. destruct H6 as [_ H6]. specialize (H6 (-lb)). replace (-lub >= lb) with (lub <= -lb).
    2 : { apply EquivThenEqual. lra. } apply H6. intros x H8. specialize (H7 (-x)). specialize (H3 (-x)).
    rewrite Ropp_involutive in H3. apply H3 in H8. specialize (H7 H8). lra.
Qed.

Lemma lub_unique : forall (E:Ensemble ℝ) a b, is_lub E a -> is_lub E b -> a = b.
Proof.
  intros E a b [H1 H2] [H3 H4]. specialize (H4 a H1). specialize (H2 b H3). lra.
Qed.

Lemma glb_unique : forall (E:Ensemble ℝ) a b, is_glb E a -> is_glb E b -> a = b.
Proof.
  intros E a b [H1 H2] [H3 H4]. specialize (H4 a H1). specialize (H2 b H3). lra.
Qed.

Lemma lub_gt_In : forall E a x, is_lub E a -> x ∈ E -> x <= a.
Proof.
  intros E a x [H1 H2] H3. specialize (H1 x H3). lra.
Qed.

Lemma glb_lt_In : forall E a x, is_glb E a -> x ∈ E -> x >= a.
Proof.
  intros E a x [H1 H2] H3. specialize (H1 x H3). lra.
Qed.

Lemma exists_lub_set_not_empty : forall (E:Ensemble ℝ) (a:R), is_lub E a -> E ≠ ∅.
Proof.
  intros E a [H1 H2]. intros H3. assert (H4 : is_upper_bound E (a-1)).
  { intros x H4. specialize (H1 x H4). autoset. }
  specialize (H2 (a-1) H4). lra.
Qed.

Lemma exists_glb_set_not_empty : forall (E:Ensemble ℝ) (a:R), is_glb E a -> E ≠ ∅.
Proof.
  intros E a [H1 H2]. intros H3. assert (H4 : is_lower_bound E (a+1)).
  { intros x H4. specialize (H1 x H4). autoset. }
  specialize (H2 (a+1) H4). lra.
Qed.

Lemma lub_eq_glb_diff_lt_eps : forall (E1 E2 : Ensemble ℝ) (a ε : ℝ),
  is_lub E1 a -> is_glb E2 a -> ε > 0 -> exists x1 x2, x1 ∈ E1 /\ x2 ∈ E2 /\ x2 - x1 < ε.
Proof.
  intros E1 E2 a ε H1 H2 H3. pose proof classic (a ∈ E1) as [H4 | H4]; pose proof classic (a ∈ E2) as [H5 | H5].
  - exists a, a. repeat split; auto. lra.
  - pose proof classic (forall x, 0 < x < ε -> (x + a) ∉ E2) as [H6 | H6].
    -- assert (is_lower_bound E2 (a + ε)) as H7.
       {
         intros x H7. assert (x >= a + ε \/ x < a + ε) as [H8 | H8] by lra; auto. pose proof Rtotal_order x a as [H9 | [H9 | H9]].
         - pose proof glb_lt_In E2 a x H2 H7 as H10. lra.
         - subst. tauto.
         - specialize (H6 (x - a) ltac:(lra)). replace (x - a + a) with x in H6 by lra. tauto.
       }
       destruct H2 as [_ H2]. specialize (H2 (a + ε) H7). lra.
    -- apply not_all_ex_not in H6 as [x H6]. apply imply_to_and in H6 as [H6 H7]. assert ((x + a) ∈ E2) as H8 by tauto.
       exists a, (x + a). repeat split; auto. lra.
  - pose proof classic (forall x, 0 < x < ε -> (a - x) ∉ E1) as [H6 | H6].
    -- assert (is_upper_bound E1 (a - ε)) as H7.
       {
         intros x H7. assert (x <= a - ε \/ x > a - ε) as [H8 | H8] by lra; auto. pose proof Rtotal_order x a as [H9 | [H9 | H9]].
         - specialize (H6 (a - x) ltac:(lra)). replace (a - (a - x)) with x in H6 by lra. tauto.
         - subst. tauto.
         - pose proof lub_gt_In E1 a x H1 H7 as H10. assert (x = a) as H11 by lra. subst. tauto.
       }
       destruct H1 as [_ H1]. specialize (H1 (a - ε) H7). lra.
    -- apply not_all_ex_not in H6 as [x H6]. apply imply_to_and in H6 as [H6 H7]. assert ((a - x) ∈ E1) as H8 by tauto.
       exists (a - x), a. repeat split; auto. lra.
  - pose proof classic (forall x, 0 < x < ε/2 -> (a - x) ∉ E1) as [H6 | H6]; pose proof classic (forall x, 0 < x < ε/2 -> (x + a) ∉ E2) as [H7 | H7].
    -- assert (is_upper_bound E1 (a - ε/2)) as H8.
       {
         intros x H8. assert (x <= a - ε/2 \/ x > a - ε/2) as [H9 | H9] by lra; auto. pose proof Rtotal_order x a as [H10 | [H10 | H10]].
         - specialize (H6 (a - x) ltac:(lra)). replace (a - (a - x)) with x in H6 by lra. tauto.
         - subst. tauto.
         - pose proof lub_gt_In E1 a x H1 H8 as H11. assert (x = a) as H12 by lra. subst. tauto.
       }
       destruct H1 as [_ H1]. specialize (H1 (a - ε/2) H8) as H9. lra.
    -- assert (is_upper_bound E1 (a - ε/2)) as H8.
       {
         intros x H8. assert (x <= a - ε/2 \/ x > a - ε/2) as [H9 | H9] by lra; auto. pose proof Rtotal_order x a as [H10 | [H10 | H10]].
         - specialize (H6 (a - x) ltac:(lra)). replace (a - (a - x)) with x in H6 by lra. tauto.
         - subst. tauto.
         - pose proof lub_gt_In E1 a x H1 H8 as H11. assert (x = a) as H12 by lra. subst. tauto.
       }
       destruct H1 as [_ H1]. specialize (H1 (a - ε/2) H8) as H9. lra.
    -- assert (is_lower_bound E2 (a + ε/2)) as H8.
       {
         intros x H8. assert (x >= a + ε/2 \/ x < a + ε/2) as [H9 | H9] by lra; auto. pose proof Rtotal_order x a as [H10 | [H10 | H10]].
         - pose proof glb_lt_In E2 a x H2 H8 as H11. lra.
         - subst. tauto.
         - specialize (H7 (x - a) ltac:(lra)). replace (x - a + a) with x in H7 by lra. tauto.
       }
       destruct H2 as [_ H2]. specialize (H2 (a + ε/2) H8) as H9. lra.
    -- apply not_all_ex_not in H6 as [x H6]. apply imply_to_and in H6 as [H6 H10]. assert ((a - x) ∈ E1) as H11 by tauto.
       apply not_all_ex_not in H7 as [y H7]. apply imply_to_and in H7 as [H7 H12]. assert ((y + a) ∈ E2) as H13 by tauto.
       exists (a - x), (y + a). repeat split; auto. lra.
Qed.

Lemma sup_le_inf : forall (E1 E2 : Ensemble ℝ) a b, is_lub E1 a -> is_glb E2 b ->
  (forall x y, x ∈ E1 -> y ∈ E2 -> x <= y) -> a <= b.
Proof.
  intros E1 E2 a b H1 H2 H3. assert (a <= b \/ a > b) as [H4 | H4]; try lra.
  pose proof classic (a ∈ E1) as [H5 | H5]; pose proof classic (b ∈ E2) as [H6 | H6].
  - specialize (H3 a b H5 H6). lra.
  - pose proof classic (forall x, 0 < x < a - b -> (b + x) ∉ E2) as [H7 | H7].
    -- assert (is_lower_bound E2 a) as H8.
       {
         intros x H8. assert (x >= a \/ x < a) as [H9 | H9] by lra; auto. pose proof Rtotal_order x b as [H10 | [H10 | H10]].
         - pose proof glb_lt_In E2 b x H2 H8 as H11. lra.
         - subst. tauto.
         - specialize (H7 (x - b) ltac:(lra)). replace (b + (x - b)) with x in H7 by lra. tauto.
       }
       destruct H2 as [_ H2]. specialize (H2 a H8). lra.
    -- apply not_all_ex_not in H7 as [x H7]. apply imply_to_and in H7 as [H7 H8]. assert ((b + x) ∈ E2) as H9 by tauto.
       specialize (H3 a (b + x) H5 H9). lra.
  - pose proof classic (forall x, 0 < x < a - b -> (a - x) ∉ E1) as [H7 | H7].
    -- assert (is_upper_bound E1 b) as H8.
       { intros x H8. assert (x <= b \/ x > b) as [H9 | H9] by lra; auto. }
       destruct H1 as [_ H1]. specialize (H1 b H8). lra.
    -- apply not_all_ex_not in H7 as [x H7]. apply imply_to_and in H7 as [H7 H8]. assert ((a - x) ∈ E1) as H9 by tauto.
       specialize (H3 (a - x) b H9 H6). lra.
  - pose proof classic (forall x, 0 < x < (a - b)/2 -> (a - x) ∉ E1) as [H7 | H7]; pose proof classic (forall x, 0 < x < (a - b)/2 -> (b + x) ∉ E2) as [H8 | H8].
    -- assert (is_upper_bound E1 ((a + b) / 2)) as H9.
       {
          intros x H9. assert (x <= (a + b) / 2 \/ x > (a + b) / 2) as [H10 | H10] by lra; auto. pose proof Rtotal_order x a as [H11 | [H11 | H11]].
          - specialize (H7 (a - x) ltac:(lra)). replace (a - (a - x)) with x in H7 by lra. tauto.
          - subst. tauto.
          - pose proof lub_gt_In E1 a x H1 H9 as H12. lra.
       }
       destruct H1 as [_ H1]. specialize (H1 ((a + b) / 2) H9). lra.
    -- assert (is_upper_bound E1 ((a + b) / 2)) as H9.
       {
          intros x H9. assert (x <= (a + b) / 2 \/ x > (a + b) / 2) as [H10 | H10] by lra; auto. pose proof Rtotal_order x a as [H11 | [H11 | H11]].
          - specialize (H7 (a - x) ltac:(lra)). replace (a - (a - x)) with x in H7 by lra. tauto.
          - subst. tauto.
          - pose proof lub_gt_In E1 a x H1 H9 as H12. lra.
       }
       destruct H1 as [_ H1]. specialize (H1 ((a + b) / 2) H9). lra.
    -- assert (is_lower_bound E2 ((a + b) / 2)) as H9.
       {
          intros x H9. assert (x >= (a + b) / 2 \/ x < (a + b) / 2) as [H10 | H10] by lra; auto. pose proof Rtotal_order x b as [H11 | [H11 | H11]].
          - pose proof glb_lt_In E2 b x H2 H9 as H12. lra.
          - subst. tauto.
          - specialize (H8 (x - b) ltac:(lra)). replace (b + (x - b)) with x in H8 by lra. tauto.
       }
       destruct H2 as [_ H2]. specialize (H2 ((a + b) / 2) H9). lra.
    -- apply not_all_ex_not in H7 as [x H7]. apply imply_to_and in H7 as [H7 H9]. assert ((a - x) ∈ E1) as H10 by tauto.
       apply not_all_ex_not in H8 as [y H8]. apply imply_to_and in H8 as [H8 H11]. assert ((b + y) ∈ E2) as H12 by tauto.
       specialize (H3 (a - x) (b + y) H10 H12). lra.
Qed.