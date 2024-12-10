Require Import Imports Sets Notations.

Import SetNotations.

Definition Relation (A B : Type) := A -> B -> Prop.

Definition Reflexive {A} (R : Relation A A) : Prop := forall x, R x x.
Definition Symmetric {A} (R : Relation A A) : Prop := forall x y, R x y -> R y x.
Definition Transitive {A} (R : Relation A A) : Prop := forall x y z, R x y -> R y z -> R x z.
Definition Antisymmetric {A} (R : Relation A A) : Prop := forall x y, R x y -> R y x -> x = y.

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

Notation "❴ ( x , y ) ∈ U ⨯ V | P ❵" := 
  (@mk_relation U V (fun (x:U) (y:V) => P))
  (at level 200).

Section section_20_1.
  Let R := ❴(x, y) ∈ ℝ ⨯ ℝ | x * y < 0 ❵.

End section_20_1.