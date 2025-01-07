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