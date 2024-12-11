Require Import Imports Sets Notations.

Import SetNotations.

Definition Relation (A B : Type) := A -> B -> Prop.

Definition Reflexive {A} (R : Relation A A) : Prop := forall x, R x x.
Definition Symmetric {A} (R : Relation A A) : Prop := forall x y, R x y -> R y x.
Definition Transitive {A} (R : Relation A A) : Prop := forall x y z, R x y -> R y z -> R x z.
Definition Antisymmetric {A} (R : Relation A A) : Prop := forall x y, R x y -> R y x -> x = y.

Definition Reflexive_On {A} (R : Relation A A) (E : Ensemble A) : Prop := 
  forall x, x ∈ E -> R x x.

Definition Symmetric_On {A} (R : Relation A A) (E : Ensemble A) : Prop :=
  forall x y, x ∈ E -> y ∈ E -> R x y -> R y x.

Definition Transitive_On {A} (R : Relation A A) (E : Ensemble A) : Prop :=
  forall x y z, x ∈ E -> y ∈ E -> z ∈ E -> R x y -> R y z -> R x z.

Definition Antisymmetric_On {A} (R : Relation A A) (E : Ensemble A) : Prop :=
  forall x y, x ∈ E -> y ∈ E -> R x y -> R y x -> x = y.

Lemma Relation_is_Ensemble : forall A B, Relation A B = Ensemble (A * B).
Proof.
  intros A B.
  apply univalence.
  exists (fun (r : Relation A B) (p : A * B) => r (fst p) (snd p)),
      (fun (e : Ensemble (A * B)) (x : A)(y : B) => e (x,y)).
  split; intros x.
  - constructor.
  - apply functional_extensionality. intros p. destruct p. reflexivity. 
Qed.

Coercion rel_to_ens {A B} (R : Relation A B) : Ensemble (A * B) := 
  fun p => R (fst p) (snd p).
Coercion ens_to_rel {A B} (E : Ensemble (A * B)) : Relation A B := 
  fun x y => E (x,y).

Lemma ens_rel_ens_id : forall A B (E : Ensemble (A * B)),
  rel_to_ens (ens_to_rel E) = E.
Proof.
  intros A B E. apply set_equal_def. intros [x y]. tauto.
Qed.

Lemma rel_ens_rel_id : forall A B (R : Relation A B),
  ens_to_rel (rel_to_ens R) = R.
Proof.
  auto.
Qed.
  
Lemma x_y_In_implies_rel : forall A B (R : Relation A B) x y, (x, y) ∈ R <-> R x y.
Proof.
  intros; split; auto.
Qed.

Definition mk_relation {U V} (f : U -> V -> Prop) : Relation U V := f.

Module RelationNotations.
  Declare Scope relation_scope.
  Delimit Scope relation_scope with rel.

  Notation "❴ ( x , y ) ∈ U ⨯ V | P ❵" := 
    (@mk_relation U V (fun (x:U) (y:V) => P))
    (at level 200).
End RelationNotations.

Lemma tessssst : forall (U : Type) (A : Ensemble U),
  forall x : (subType A), val A x ∈ A.
Proof.
  intros U A [x prop]; auto.
Qed.

Lemma test2 : forall (U : Type) (A : Ensemble U),
  forall x : U, x ∈ A -> exists (y : subType A) H, y = mkSubType U A x H.
Proof.
  intros U A x H1. exists (mkSubType U A x H1). exists H1. reflexivity.
Qed.

Lemma subType_eqivalence_proof_irrelevance : 
  forall (U : Type) (A : Ensemble U) (x : U) (H1 H2 : x ∈ A),
    mkSubType U A x H1 = mkSubType U A x H2.
Proof.
  intros U A x H1 H2. replace H1 with H2. reflexivity. apply proof_irrelevance.
Qed.