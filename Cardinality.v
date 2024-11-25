Require Import Imports Sets Function.
Import SetNotations.

Open Scope R_scope.

Record subType {A : Type} (E : Ensemble A) : Type := mkSubType {
  x : A;
  property : x ∈ E
}.

Definition eq_cardinality {A B : Type} (X : Ensemble A) (Y : Ensemble B) : Prop :=
  exists f : subType X -> subType Y, bijective f.

Notation "‖ X ‖ = ‖ Y ‖" := (eq_cardinality X Y) (at level 70, format "‖ X ‖  =  ‖ Y ‖").
(*Notation "‖ X ‖ ≠ ‖ Y ‖" := (neq_cardinality X Y) (at level 70, format "‖ X ‖  ≠  ‖ Y ‖").*)

Open Scope Z_scope.

Lemma  : 
Proof.
Qed.

Theorem theorem_29_4 : ‖(Full_set nat)‖ = ‖(Full_set Z)‖.
Proof.
  set (f := fun n : subType (Full_set nat) => mkSubType Z (Full_set Z) ((1 + (-1)^(Z.of_nat (x (Full_set nat) n)) * (2 * (Z.of_nat (x (Full_set nat) n)) - 1)/4))).
  exists f. split.
  - intros x y H1. admit.
  - intros y. admit.
Abort.