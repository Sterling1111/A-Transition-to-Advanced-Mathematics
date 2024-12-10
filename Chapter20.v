Require Import Imports Sets Notations.

Import SetNotations.

Require Export Chapter19.

Lemma Relation_is_Ensemble : forall A, Relation A = Ensemble (A * A).
Proof.
  intros A.
  apply univalence.
  exists (fun (r : Relation A) (p : A * A) => r (fst p) (snd p)),
      (fun (e : Ensemble (A * A)) (x y : A) => e (x,y)).
  split; intros H1.
  - apply functional_extensionality; intros p.
    constructor; intros H2; destruct p; simpl in *; auto.
  - apply functional_extensionality; intros p. replace (fst p, snd p) with p; tauto.
Qed.

Coercion rel_to_ens {A} (R : Relation A) : Ensemble (A * A) := 
  fun p => R (fst p) (snd p).

Coercion ens_to_rel {A} (E : Ensemble (A * A)) : Relation A := 
  fun x y => E (x,y).

Lemma ens_rel_ens_id : forall A (E : Ensemble (A * A)),
  rel_to_ens (ens_to_rel E) = E.
Proof.
  intros A E. apply set_equal_def. intros p; destruct p; split; auto.
Qed.

Lemma rel_ens_rel_id : forall A (R : Relation A),
  ens_to_rel (rel_to_ens R) = R.
Proof.
  intros A E. unfold ens_to_rel, rel_to_ens. apply functional_extensionality; intros x.
  apply functional_extensionality; intros y. reflexivity.
Qed.
  
Open Scope R_scope.

Lemma x_y_In_implies_rel : forall A (R : Relation A) x y, (x, y) ∈ R <-> R x y.
Proof.
  intros; split; auto.
Qed.

Section section_20_1.
  Open Scope R_scope.

  Let A : Ensemble ℝ := ⦃ 1, 2, 3, 4, 5, 6 ⦄.
  Let R : Relation ℝ := ⦃ (1,1),(1,2),(1,3),(1,4),(2,3),(2,5),(2,6),(3,5),(4,5),(4,6) ⦄.
  
  Let S (n : subType A) : Ensemble ℝ := (fun x => (val A n, x) ∈ R).

  Lemma lemma_20_1_a : R 1 1.
  Proof.
    apply x_y_In_implies_rel. unfold R; rewrite ens_rel_ens_id. autoset.
  Qed.

  Lemma lemma_20_1_b : ~ R 2 1.
  Proof.
    assert (H1 : (2,1) ∉ R). { unfold R; rewrite ens_rel_ens_id. autoset. } auto.
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

Definition Antisymmetric {A} (R : Relation A) : Prop :=
  forall x y, R x y -> R y x -> x = y.

Notation "❴ ( x , y ) : U * V | P ❵" := (fun p : U * V => let '(x, y) := p in P)
  (at level 200, x, y at level 99, U, V at level 30, P at level 200, format "❴ ( x , y ) : U * V | P ❵") : set_scope.

Section section_20_3.
  Let R : Relation ℝ := fun x y => x * y < 0.

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
  Let R : Relation ℝ := fun x y => exists z : Z, IZR z = x - y.

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
  Let R : Relation ℤ := fun a b => Z.Even (a - b).

  
  
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