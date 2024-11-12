Require Import Imports Sequence Sets.
Import SetNotations.

Definition limit (f : R -> R) (D : Ensemble R) (c L : R) : Prop := 
  forall ε : R, ε > 0 ->
    exists δ : R, δ > 0 /\
      forall x : R, x ∈ D /\ 0 < |x - c| < δ -> |f x - L| < ε.

