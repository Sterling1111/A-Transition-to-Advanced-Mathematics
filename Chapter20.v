Require Import Imports Sets.

Import SetNotations.

Require Export Chapter19.

(* this could create inconsistency so in general dont do it. 
   However for this project I prefer convinience over consistency *)

Axiom univalence : forall (A B : Type), (A = B) <-> exists (f : A -> B) (g : B -> A),
  (forall x, g (f x) = x) /\ (forall y, f (g y) = y).

Axiom EquivThenEqual: prop_extensionality.

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

  Inductive A := one | two | three | four | five | six.

  Notation "1" := one.
  Notation "2" := two.
  Notation "3" := three.
  Notation "4" := four.
  Notation "5" := five.
  Notation "6" := six.

  Let R : Relation A := ⦃ (1,1),(1,2),(1,3),(1,4),(2,3),(2,5),(2,6),(3,5),(4,5),(4,6) ⦄.

  Definition S (n : A) : Ensemble A := (fun x => (R n x)).

  Lemma lemma_20_1_a : R 1 1.
  Proof.
    apply x_y_In_implies_rel. unfold R. rewrite ens_rel_ens_id. autoset.
  Qed.

  Lemma lemma_20_1_b : ~ R 2 1.
  Proof.
    assert (H1 : (2,1) ∉ R). { unfold R. rewrite ens_rel_ens_id. autoset. } auto.
  Qed.

  Lemma S1_elements : S 1 = ⦃ 1, 2, 3, 4 ⦄.
  Proof.
    unfold S, R. apply functional_extensionality. intros x. destruct x.
    - apply EquivThenEqual. split; intros. replace (⦃1,2,3,4⦄ 1) with (1 ∈ ⦃1,2,3,4⦄); autoset.
      apply x_y_In_implies_rel. rewrite ens_rel_ens_id. autoset.
    - apply EquivThenEqual. split; intros. replace (⦃1,2,3,4⦄ 2) with (2 ∈ ⦃1,2,3,4⦄); autoset.
      apply x_y_In_implies_rel. rewrite ens_rel_ens_id. autoset.
    - admit.
    - admit.
    - apply EquivThenEqual. split; intros. apply x_y_In_implies_rel in H.
      assert (~(1, 5) ∈ ⦃(1, 1),(1, 2),(1, 3),(1, 4),(2, 3),(2, 5),(2, 6),(3, 5),(4, 5),(4, 6)⦄). { autoset. } tauto.
      assert (~5 ∈ ⦃1,2,3,4⦄). { autoset. } tauto.
    - admit.
Admitted.

End section_20_1.

Section yuckk.
  Let A := {x : R | x <> 0}.
  Let Rel : Relation A := fun x y => proj1_sig x * proj1_sig y > 0.

  Lemma eating_cats : Equivalence Rel.
  Proof.
    constructor.
    - intros x. unfold Rel. destruct x; simpl. nra.
    - intros x y. unfold Rel. destruct x, y; simpl. nra.
    - intros x y z. unfold Rel. destruct x, y, z; simpl. nra.
  Qed.
End yuckk.

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