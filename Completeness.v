Require Import Imports.

Open Scope R_scope.

Definition is_lower_bound (E:R -> Prop) (m:R) := forall x:R, E x -> x >= m.

Definition has_lower_bound (E:R -> Prop) := exists m : R, is_lower_bound E m.

Definition is_glb (E:R -> Prop) (m:R) :=
  is_lower_bound E m /\ (forall b:R, is_lower_bound E b -> m >= b).

Lemma completeness_lower_bound :
    forall E:R -> Prop,
      has_lower_bound E -> (exists x : R, E x) -> { m:R | is_glb E m }.
Proof.
  intros E Hbounded Hexists.
  pose (E' := fun x => E (-x)).
  assert (Hbounded' : bound E').
  {
    unfold bound, is_upper_bound, E'.
    destruct Hbounded as [m Hm].
    exists (-m).
    intros x Ex.
    specialize (Hm (-x) Ex).
    lra.
  }
  assert (Hexists' : exists x:R, E' x).
  {
    destruct Hexists as [x Ex].
    exists (-x). unfold E'. rewrite Ropp_involutive. exact Ex.
  }
  destruct (completeness E' Hbounded' Hexists') as [m' Hm'].
  exists (-m'). unfold is_glb, is_lower_bound.
  split.
  - intros x Ex. destruct Hm' as [Hup _]. unfold E', is_upper_bound in Hup.
    specialize (Hup (-x)). apply Ropp_ge_cancel. rewrite Ropp_involutive. 
    rewrite Ropp_involutive in Hup. apply Rle_ge. apply Hup. apply Ex.
  - intros b Hlow. destruct Hm' as [_ Hleast]. unfold is_upper_bound in Hleast.
    assert (H : forall r1 r2 : R, r1 <= - r2 -> - r1 >= r2).
    { intros r1 r2. lra. } apply H.
    apply Hleast. 
    assert (H2 : forall r1 r2 : R, -r1 >= r2 -> r1 <= - r2).
    { intros r1 r2. lra. } intros x H3. apply H2. apply Hlow.
    unfold E' in H3. apply H3.
Qed.