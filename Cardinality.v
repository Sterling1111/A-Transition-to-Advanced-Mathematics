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

Lemma eq_cardinality_Full_set : forall (A B : Type),
  (exists f : A -> B, bijective f) -> ‖(Full_set A)‖ = ‖(Full_set B)‖.
Proof.
  intros A B [f [H1 H2]]. unfold injective in H1. unfold surjective in H2.
  unfold eq_cardinality.
  exists (fun sa : subType (Full_set A) => mkSubType B (Full_set B) (f (x _ sa)) ltac:(apply Full_intro)).
  split.
  - intros x y H3. destruct x as [x H4], y as [y H5]. simpl in *. specialize (H1 x y).
    specialize (H1 ltac:(inversion H3; reflexivity)). subst. replace H4 with H5.
    2 : { destruct H4, H5. reflexivity. } reflexivity.
  - intros y. destruct y as [y H3]. specialize (H2 y) as [x H4]. exists (mkSubType A (Full_set A) x ltac:(apply Full_intro)).
    simpl. destruct H3, H4. reflexivity.
Qed.

Theorem theorem_29_4 : ‖(Full_set nat)‖ = ‖(Full_set Z)‖.
Proof.
  apply eq_cardinality_Full_set.
  set (f := fun n : nat => if Nat.even n then Z.of_nat (n / 2) else - Z.of_nat (n / 2 + 1)).
  exists f. split.
  - intros x y H1. unfold f in H1. destruct (Nat.even x) eqn:H2, (Nat.even y) eqn:H3.
    -- apply Nat.even_spec in H2 as [j H2], H3 as [k H3]; subst. apply Nat2Z.inj in H1.
       do 2 (rewrite Nat.mul_comm, Nat.div_mul in H1; try lia).
    -- 
Abort.