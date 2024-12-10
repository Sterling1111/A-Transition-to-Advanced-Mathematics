Require Import Imports Sets Relations Notations.
Import SetNotations.
Require Export Chapter19.

Open Scope R_scope.
Set Printing Coercions.

Section section_20_1.
  Let A : Ensemble ℝ := ⦃ 1, 2, 3, 4, 5, 6 ⦄.
  Let R : Relation ℝ ℝ := ⦃ (1,1),(1,2),(1,3),(1,4),(2,3),(2,5),(2,6),(3,5),(4,5),(4,6) ⦄.
  
  Let S (n : subType A) : Ensemble ℝ := (fun x => (val A n, x) ∈ R).

  Lemma lemma_20_1_a : R 1 1.
  Proof.
    unfold R. rewrite <- x_y_In_implies_rel. autoset.
  Qed.

  Lemma lemma_20_1_b : ~ R 2 1.
  Proof.
    unfold R. rewrite <- x_y_In_implies_rel. rewrite ens_rel_ens_id. autoset.
  Qed.

  Let one := mkSubType _ A 1 ltac:(unfold A; autoset).
  Let two := mkSubType _ A 2 ltac:(unfold A; autoset).
  Let three := mkSubType _ A 3 ltac:(unfold A; autoset).
  Let four := mkSubType _ A 4 ltac:(unfold A; autoset).
  Let five := mkSubType _ A 5 ltac:(unfold A; autoset).
  Let six := mkSubType _ A 6 ltac:(unfold A; autoset).

  Lemma S_elements : S one = ⦃ 1, 2, 3, 4 ⦄ /\ S two = ⦃ 3, 5, 6 ⦄ /\ S three = ⦃ 5 ⦄ /\ S four = ⦃ 5, 6 ⦄ /\ S five = ∅ /\ S six = ∅.
  Proof. repeat split; clear; unfold S, R; rewrite ens_rel_ens_id; autoset.  Qed.

End section_20_1. 

Section section_20_3.
  Let R : Relation ℝ ℝ := fun x y => x * y < 0.

  Lemma lemma_20_3_c_1 : ~ Reflexive R.
  Proof.
    intros H1. unfold Reflexive in H1. specialize (H1 1). unfold R in H1. lra.
  Qed. 

  Lemma lemma_20_3_c_2 : Symmetric R.
  Proof.
    intros x y H1. unfold R in *. lra.
  Qed.

  Lemma lemma_20_3_c_3 : ~ Transitive R.
  Proof.
    intros H1. unfold Transitive in H1. specialize (H1 (-1) 1 (-1)). unfold R in H1. lra.
  Qed.

  Lemma lemma_20_c_c_4 : ~ Antisymmetric R.
  Proof.
    intros H1. specialize (H1 1 (-1)). unfold R in H1. lra.
  Qed.
End section_20_3.

Section section_20_4.
  Let R : Relation ℝ ℝ := fun x y => exists z : Z, IZR z = x - y.

  Lemma lemma_20_4_c_1 : Reflexive R.
  Proof.
    intros x. exists 0%Z. lra.
  Qed.

  Lemma lemma_20_4_c_2 : Symmetric R.
  Proof.
    intros x y [z H1]. exists (-z)%Z. rewrite opp_IZR. lra.
  Qed.

  Lemma lemma_20_4_c_3 : Transitive R.
  Proof.
    intros x y z [m H1] [n H2]. exists (m + n)%Z. rewrite plus_IZR. lra.
  Qed.

  Lemma lemma_20_4_c_4 : ~Antisymmetric R.
  Proof.
    intros H1. specialize (H1 1 2 ltac:(exists (-1)%Z; lra) ltac:(exists 1%Z; lra)). lra.
  Qed.
End section_20_4.

Section section_20_5.
  Let R : Relation ℤ ℤ := fun a b => Z.Even (a - b).

  
  
End section_20_5.

Definition disjoint_pieces {A} (P : Ensemble (Ensemble A)) : Prop :=
  forall E1 E2, E1 ∈ P -> E2 ∈ P -> E1 ⋂ E2 = ∅.
Definition nonempty_pieces {A} (P : Ensemble (Ensemble A)) : Prop :=
  forall E, E ∈ P -> E ≠ ∅.
Definition covering {A} (P : Ensemble (Ensemble A)) : Prop :=
  forall x : A, exists E, E ∈ P /\ x ∈ E.
Definition partition {A} (E : Ensemble (Ensemble A)) : Prop :=
  disjoint_pieces E /\ nonempty_pieces E /\ covering E.
Definition Forall_Ensemble {A : Type} (E : Ensemble A) (P : A -> Prop) :=
  forall x, x ∈ E -> P x.
Definition Ensemble_map {A B} (f : A -> B) (E : Ensemble A) : Ensemble B :=
  fun y => exists x, x ∈ E /\ y = f x.
Section testsection.
  Definition Ensemble_to_Type {A} (E : Ensemble A) : Type := {x : A | x ∈ E}.
  Definition E := ⦃⦃1, 2, 3⦄, ⦃4, 5, 6⦄, ⦃7, 8, 9⦄⦄.
  Definition E' := Ensemble_map (fun x => Ensemble_to_Type x) E.
  Theorem pasting_together_theorem : forall {A B : Type} (P : Ensemble (Ensemble A)) (Q : Ensemble (Ensemble B)),
    partition P -> partition Q -> exists R : (Ensemble (Type -> Type)), 2 + 2 = 4.
  Proof.
    intros. exists ⦃⦄. lra.
  Qed.
End testsection.