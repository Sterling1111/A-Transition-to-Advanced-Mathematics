Require Import Imports Sets.
Import SetNotations.

Open Scope set_scope.

Lemma eq_cardinality_Full_set : forall (A B : Type),
  (exists f : A -> B, bijective f) -> ‖Full_set A‖ = ‖Full_set B‖.
Proof.
  intros A B [f [H1 H2]]. unfold injective in H1. unfold surjective in H2.
  unfold cardinal_eq.
  exists (fun sa : subType (Full_set A) => mkSubType B (Full_set B) (f (val _ sa)) ltac:(apply Full_intro)).
  split.
  - intros x y H3. destruct x as [x H4], y as [y H5]. simpl in *. specialize (H1 x y).
    specialize (H1 ltac:(inversion H3; reflexivity)). subst. replace H4 with H5.
    2 : { destruct H4, H5. reflexivity. } reflexivity.
  - intros y. destruct y as [y H3]. specialize (H2 y) as [x H4]. exists (mkSubType A (Full_set A) x ltac:(apply Full_intro)).
    simpl. destruct H3, H4. reflexivity.
Qed.

Coercion Type_to_Ensemble (A : Type) : Ensemble A :=
  Full_set A.

Coercion Ensemble_to_Type (A : Type) (X : Ensemble A) : Type :=
  subType X.

Lemma Type_Ensemble_Type : forall A : Type,
  Ensemble_to_Type A (Type_to_Ensemble A) = A.
Proof.
  intros A. unfold Ensemble_to_Type. unfold Type_to_Ensemble. apply univalence.
  set (f := fun x : (subType (Full_set A)) => val (Full_set A) x ).
  set (g := fun x : A => mkSubType A (Full_set A) x ltac:(apply Full_intro)).
  exists f, g. split; intros; unfold f, g.
  - destruct x as [x H1]. simpl. destruct H1. reflexivity.
  - unfold f, g. reflexivity.
Qed.

Lemma Ensemble_Type_Ensemble : forall A (X : Ensemble A),
  Type_to_Ensemble (Ensemble_to_Type A X) = X.
Proof.
  auto.
Qed.

Lemma eq_cardinality_Full_set_Type : forall (A B : Type),
  ‖A‖ = ‖B‖ <-> ‖Full_set A‖ = ‖Full_set B‖.
Proof.
  intros A B. split; intro H1; unfold Type_to_Ensemble in H1; auto.
Qed.

Lemma eq_cardinality_Type : forall A B : Type,
  (exists f : A -> B, bijective f) -> ‖A‖ = ‖B‖.
Proof.
  intros A B [f H1]. apply eq_cardinality_Full_set. exists f. auto.
Qed.

Lemma subType_Full_set : forall A : Type,
  subType (Full_set A) = A.
Proof.
  intros A. apply univalence.
  set (f := fun x : (subType (Full_set A)) => val (Full_set A) x ).
  set (g := fun x : A => mkSubType A (Full_set A) x ltac:(apply Full_intro)).
  exists f, g. split; intros; unfold f, g.
  - destruct x as [x H1]. simpl. destruct H1. reflexivity.
  - unfold f, g. reflexivity.
Qed.

Lemma image_card : forall A B (f : A -> B),
  Finite_set A -> ‖ image f ‖ <= ‖ A ‖.
Proof.
  intros A B f [l H1]. unfold cardinal_le, image. rewrite subType_Full_set.
  set (g := map f l). set (E := list_to_ensemble g). exists E. split.

Abort.

Theorem theorem_28_1 : forall A B (f : A -> B),
  Finite_set (Full_set A) -> ‖ image f ‖ <= ‖ (Full_set A) ‖.
Proof.
  intros A B f H1.
Abort.