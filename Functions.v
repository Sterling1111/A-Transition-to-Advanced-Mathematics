Require Import Imports Sets.
Import SetNotations.

Open Scope set_scope.

Definition injective {A B : Type} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Definition surjective {A B : Type} (f : A -> B) : Prop :=
  forall y : B, exists x : A, f x = y.

Definition bijective {A B : Type} (f : A -> B) : Prop :=
  injective f /\ surjective f.

Definition image {A B : Type} (f : A -> B) : Ensemble B :=
  fun y : B => exists x : A,  f x = y.

Theorem theorem_28_1 : forall A B (f : A -> B),
  Finite_set (Full_set A) -> ‖ image f ‖ <= ‖ (Full_set A) ‖.
Proof.
  
Abort.

