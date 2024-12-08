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
  Let T := subType A.
  Let R : Relation ℝ := ⦃ (1,1),(1,2),(1,3),(1,4),(2,3),(2,5),(2,6),(3,5),(4,5),(4,6) ⦄.
  
  Let S (n : T) : Ensemble ℝ := (fun x => (val A n, x) ∈ R).

  Lemma lemma_20_1_a : R 1 1.
  Proof.
    apply x_y_In_implies_rel. unfold R; rewrite ens_rel_ens_id. autoset.
  Qed.

  Lemma lemma_20_1_b : ~ R 2 1.
  Proof.
    assert (H1 : (2,1) ∉ R). { unfold R; rewrite ens_rel_ens_id. autoset. } auto.
  Qed.

  Let one : T := mkSubType _ A 1 ltac:(unfold A; autoset).

  Lemma S1_elements : S one = ⦃ 1, 2, 3, 4 ⦄.
  Proof.
    unfold S, R; replace (val A one) with 1 by reflexivity; clear one. apply set_equal_def; intros x; split; intros H1.
    - rewrite ens_rel_ens_id in H1. 
      replace (fun x : ℝ => (1, x) ∈ ⦃(1, 1),(1, 2),(1, 3),(1, 4),(2, 3),(2, 5),(2, 6),(3, 5),(4, 5),(4, 6)⦄) with 
      (⦃1, 2, 3, 4⦄) in H1; auto. clear x H1. apply functional_extensionality. intros x.
      apply EquivThenEqual. split; intros H1.
      -- assert (x = 1 \/ x = 2 \/ x = 3 \/ x = 4) as [H2 | [H2 | [H2 | H2]]]; subst; autoset.
         { apply In_Union_def in H1 as [H1 | H1]. left. apply In_singleton_def in H1. auto. right.
           apply In_Union_def in H1 as [H1 | H1]. left. apply In_singleton_def in H1. auto. right.
           apply In_Union_def in H1 as [H1 | H1]. left. apply In_singleton_def in H1. auto. right.
           apply In_Union_def in H1 as [H1 | H1]. apply In_singleton_def in H1. auto. autoset. }
      -- assert (x = 1 \/ x = 2 \/ x = 3 \/ x = 4) as [H2 | [H2 | [H2 | H2]]]; subst; autoset. admit.
      left. autoset. right; left. autoset. right; right; left. autoset. right; right; right. autoset.
    -  assert (x = 1 \/ x = 2 \/ x = 3 \/ x = 4) as [H2 | [H2 | [H2 | H2]]]; subst; autoset. admit.
       -- rewrite ens_rel_ens_id. left. autoset.
       -- rewrite ens_rel_ens_id. right; left. autoset.
       -- rewrite ens_rel_ens_id. right; right; left. autoset.
       -- rewrite ens_rel_ens_id. right; right; right. autoset.
  Admitted.
End section_20_1.

Section section_20_3.
  Let R : Relation ℝ := fun x y => x * y < 0.

  Lemma lemma_20_3_c_1 : Reflexive R.
  Proof.
    unfold Reflexive. intros x. unfold R. 
  Qed.
  
End section_20_3.

Section yuckk.
  Let E : Ensemble R := fun x => x <> 0.
  Let A := subType E.
  Let Rel : Relation A := fun x y : A => val E x * val E y > 0.

  Lemma eating_cats : Equivalence Rel.
  Proof.
    unfold Rel; constructor; [intros x | intros x y H1 | intros x y z H1 H2].
    - destruct x. simpl. assert (val0 <> 0) as H1 by autoset. nra.
    - nra.
    - nra.
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