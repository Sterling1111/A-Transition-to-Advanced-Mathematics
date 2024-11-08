Set Warnings "-uniform-inheritance,-ambiguous-paths".

Require Import ZArith Lia Classical Reals Lra Classical_sets List
               Ensembles QArith ClassicalFacts Finite_sets Powerset Finite_sets_facts Image 
               NArith DecimalString DecimalNat DecimalNat Decimal FunctionalExtensionality
               Fibonacci Sums Sets Binomial QRT WI_SI_WO Prime Relations_1.

Require Export Chapter19.

Import ListNotations SetNotations Choose_Notations.

Open Scope type_scope.

(* this could create inconsistency so in general dont do it. 
   However for this project I prefer convinience over consistency *)

Axiom univalence : forall (A B : Type), (A = B) <-> exists (f : A -> B) (g : B -> A),
  (forall x, g (f x) = x) /\ (forall y, f (g y) = y).

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
  Let A := ⦃ 1, 2, 3, 4, 5, 6 ⦄.
  
  Let R : Relation ℝ := ⦃ (1,1),(1,2),(1,3),(1,4),(2,3),(2,5),(2,6),(3,5),(4,5),(4,6) ⦄.

  Lemma lemma_20_1_a : R 1 1.
  Proof.
    apply x_y_In_implies_rel. unfold R. rewrite ens_rel_ens_id. autoset.
  Qed.

End section_20_1.

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