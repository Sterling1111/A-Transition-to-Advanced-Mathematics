Require Import Imports Sets.

Definition injective {A B : Type} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Definition surjective {A B : Type} (f : A -> B) : Prop :=
  forall y : B, exists x : A, f x = y.

Definition bijective {A B : Type} (f : A -> B) : Prop :=
  injective f /\ surjective f.