Require Import Imports Binomial Reals_util Utf8.

Import ListNotations Binomial.Choose_Notations.

Open Scope nat_scope.

Definition injective {A B : Type} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Definition surjective {A B : Type} (f : A -> B) : Prop :=
  forall y : B, exists x : A, f x = y.

Definition bijective {A B : Type} (f : A -> B) : Prop :=
  injective f /\ surjective f.

Definition image {A B : Type} (f : A -> B) : Ensemble B :=
  fun y : B => exists x : A,  f x = y.

Declare Scope set_scope.
Delimit Scope set_scope with set.

Module SetNotations.

Notation "x ∈ A" := (In _ A x) (at level 20) : set_scope.

Definition set_prod {U V : Type} (A : Ensemble U) (B : Ensemble V) : Ensemble (U * V) :=
  fun p => exists a b, (a ∈ A)%set /\ (b ∈ B)%set /\ p = (a, b).

Notation "x ∉ A" := (~ In _ A x) (at level 20) : set_scope.
Notation "A ⊆ B" := (Included _ A B) (at level 40) : set_scope.
Notation "A ⊈ B" := (~ Included _ A B) (at level 40) : set_scope.
Notation "A ⊊ B" := (Strict_Included _ A B) (at level 40) : set_scope.
Notation "A ⋃ B" := (Union _ A B) (at level 30) : set_scope.
Notation "A ⋂ B" := (Intersection _ A B) (at level 30) : set_scope.
Notation "A − B" := (Setminus _ A B) (at level 30) : set_scope.
Notation "A × B" := (set_prod A B) (at level 30) : set_scope.
Notation "A ′" := (Complement _ A) (at level 50, format "A ′") : set_scope.
Notation "∅" := (Empty_set _) : set_scope.
Notation "‖ A ‖ = n" := (@cardinal _ A n) (at level 70, format "‖ A ‖  =  n") : set_scope.


Definition FromList {U : Type} (l : list U) : Ensemble U :=
  fun x => List.In x l.

Fixpoint list_to_ensemble {U : Type} (l : list U) : Ensemble U :=
  match l with
  | [] => ∅%set
  | x :: xs => Union U (Singleton U x) (list_to_ensemble xs)
  end.

Notation "⦃⦄" := (∅%set) : set_scope.
Notation "⦃ x ⦄" := (Singleton _ x)(format "⦃ x ⦄"): set_scope.

Notation "⦃ x , y , .. , z ⦄" :=
  (@list_to_ensemble _ (cons x (cons y .. (cons z nil) ..)))
  (format "⦃ x , y , .. , z ⦄") : set_scope.

Definition Power_set {U : Type} (A : Ensemble U) : Ensemble (Ensemble U) :=
  fun B => (B ⊆ A)%set.

Notation "ℙ( A )" := (Power_set A) (at level 20, format "ℙ( A )") : set_scope.

Definition Finite_set {U : Type} (A : Ensemble U) : Prop :=
  exists (l : list U), list_to_ensemble l = A.

Definition Finite_set' {U : Type} (A : Ensemble U) : Prop :=
  exists (l : list U), NoDup l /\ list_to_ensemble l = A.

Definition Infinite_set {U : Type} (A : Ensemble U) : Prop :=
  ~ Finite_set A.

Open Scope set_scope.

Lemma exists_no_Dup : forall (U : Type) (l : list U),
  exists (l' : list U), NoDup l' /\ (forall x, List.In x l <-> List.In x l').
Proof.
  intros U l. induction l as [| h t [l' [IH1 IH2]]].
  - exists []. split; [ apply NoDup_nil | intros; split; intros H1; inversion H1 ].
  - pose proof classic (List.In h t) as [H1 | H1].
    -- exists l'. split; auto. intros x. split; intros H2.
       * apply IH2. destruct H2 as [H2 | H2]; auto. rewrite <- H2. auto.
       * simpl. apply IH2 in H2. auto.
    -- exists (h :: l'). split. 
       * apply NoDup_cons; auto. intros H2. apply H1. apply IH2. auto.
       * intros x. split; intros [H2 | H2]; solve [left; auto | right; apply IH2; auto].
Qed.  

Record subType {A : Type} (E : Ensemble A) : Type := mkSubType {
  val : A;
  property : val ∈ E
}.

Definition cardinal_eq {U V : Type} (A : Ensemble U) (B : Ensemble V) :=
  (A = ∅ /\ B = ∅) \/
  (A ≠ ∅ /\ B ≠ ∅ /\ exists (f : subType A -> subType B), bijective f).

Definition cardinal_lt {A B : Type} (X : Ensemble A) (Y : Ensemble B) : Prop :=
  (exists f : (subType X) -> (subType Y), injective f) /\
  (~exists f : (subType X) -> (subType Y), bijective f).

Definition cardinal_le {A B : Type} (X : Ensemble A) (Y : Ensemble B) : Prop :=
  exists f : (subType X) -> (subType Y), injective f.

Notation "‖ X ‖ = ‖ Y ‖" := (cardinal_eq X Y) (at level 70, format "‖ X ‖  =  ‖ Y ‖") : set_scope.
Notation "‖ X ‖ <= ‖ Y ‖" := (cardinal_le X Y) (at level 70, format "‖ X ‖  <=  ‖ Y ‖") : set_scope.
Notation "‖ X ‖ < ‖ Y ‖" := (cardinal_lt X Y) (at level 70, format "‖ X ‖  <  ‖ Y ‖") : set_scope.
Notation "‖ X ‖ >= ‖ Y ‖" := (cardinal_le Y X) (at level 70, format "‖ X ‖  >=  ‖ Y ‖") : set_scope.
Notation "‖ X ‖ > ‖ Y ‖" := (cardinal_lt Y X) (at level 70, format "‖ X ‖  >  ‖ Y ‖") : set_scope.

End SetNotations.

Close Scope set_scope.

Import SetNotations.

Open Scope set_scope.

Lemma lemma_14_4 : forall (l : list Prop),
  ~ (fold_right and True l) -> fold_right or False (map (fun P => ~ P) l).
Proof.
  intros l H1. induction l as [| h t IH].
  - simpl in H1. exfalso. apply H1. apply I.
  - rewrite map_cons. replace ((~ h) :: map (fun P : Prop => ~ P) t) with ([~ h] ++ map (fun P : Prop => ~ P) t) by reflexivity.
    rewrite fold_right_app. simpl. replace (h :: t) with ([h] ++ t) in H1 by reflexivity. rewrite fold_right_app in H1. simpl in H1.
    apply not_and_or in H1 as [H2 | H2].
    -- left. auto.
    -- right. apply (IH H2).
Qed.

Lemma set_equal_def : forall (U : Type) (A B : Ensemble U),
  A = B <-> (forall x : U, x ∈ A <-> x ∈ B).
Proof.
  intros U A B; split; intros H1.
  - intros x; rewrite H1; reflexivity.
  - apply Extensionality_Ensembles; split; intros x H2; apply H1; auto.
Qed.

Lemma FromList_cons : forall (U : Type) (x : U) (xs : list U),
  FromList (x :: xs) = Union U (Singleton U x) (FromList xs).
Proof.
  intros U x xs. apply set_equal_def. intros y. unfold FromList. split; intros H1.
  - destruct H1 as [H1 | H1].
    + apply Union_introl. apply Singleton_intro. auto.
    + apply Union_intror. auto.
  - apply Union_inv in H1 as [H1 | H1].
    + apply Singleton_inv in H1. left. auto.
    + right. auto.
Qed.

Lemma FromList_list_to_ensemble : forall (U : Type) (l : list U),
  FromList l = list_to_ensemble l.
Proof.
  intros U l. induction l as [| x xs IH].
  - apply set_equal_def. intros x. split; intros H1; inversion H1.
  - simpl. rewrite FromList_cons. rewrite IH. reflexivity.
Qed.

Lemma list_to_ensemble_cons : forall (U : Type) (x : U) (xs : list U),
  list_to_ensemble (x :: xs) = Union U (Singleton U x) (list_to_ensemble xs).
Proof.
  intros U x xs. auto.
Qed.

Lemma not_In_Empty : forall (U : Type) (x : U),
  x ∉ ∅.
Proof.
  intros U x. intros H1. inversion H1.
Qed.

Lemma not_Empty_In : forall (U : Type) (A : Ensemble U),
  A ≠ ∅ <-> exists x, x ∈ A.
Proof.
  intros U A. split.
  - intro H1. apply not_empty_Inhabited in H1 as [x H1]. exists x. auto.
  - intros [x H1] H2. rewrite H2 in H1. inversion H1.
Qed.

Lemma Subset_refl : forall (U : Type) (A : Ensemble U),
  A ⊆ A.
Proof.
  intros U A x H1. auto.
Qed.

Lemma Empty_Subset : forall (U : Type) (A : Ensemble U),
  ∅ ⊆ A.
Proof.
  intros U A x H1. inversion H1.
Qed.

Lemma In_prod_def : forall (U V : Type) (A : Ensemble U) (B : Ensemble V) (x : U) (y : V),
  (x, y) ∈ (A × B) <-> x ∈ A /\ y ∈ B.
Proof.
  intros U V A B x y. split.
  - intros [a [b [H1 [H2 H3]]]]. inversion H3 as [[H4 H5]]. split; auto.
  - intros [H1 H2]. unfold In. exists x, y. auto.
Qed.
 
Lemma In_or_not : forall (U : Type) (A : Ensemble U) (x : U),
  x ∈ A \/ x ∉ A.
Proof.
  intros U A x. apply classic.
Qed.

Lemma subset_subset_eq_iff : forall (U : Type) (A B : Ensemble U),
  A ⊆ B /\ B ⊆ A <-> A = B.
Proof.
  intros U A B; split.
  - intros [H1 H2]. apply Extensionality_Ensembles; split; auto.
  - intros H1. rewrite H1. unfold Included. auto.
Qed.

Lemma In_Union_def : forall (U : Type) (A B : Ensemble U) (x : U),
  x ∈ (A ⋃ B) <-> x ∈ A \/ x ∈ B.
Proof.
  intros; split; [apply Union_inv | intros [H1 | H1]; [apply Union_introl; auto | apply Union_intror; auto]].
Qed.

Lemma In_Intersection_def : forall (U : Type) (A B : Ensemble U) (x : U),
  x ∈ (A ⋂ B) <-> (x ∈ A /\ x ∈ B).
Proof.
  intros; split; [apply Intersection_inv | intros [H1 H2]; apply Intersection_intro; auto].
Qed.

Lemma Complement_def : forall (U : Type) (A : Ensemble U) (x : U),
  x ∈ (A′) <-> x ∉ A.
Proof.
  intros U A x; split; auto.
Qed.

Lemma In_Setminus_def : forall (U : Type) (A B : Ensemble U) (x : U),
  x ∈ A − B <-> x ∈ A /\ x ∉ B.
Proof.
  intros U A B x; split.
  - intros H1. auto.
  - intros [H1 H2]. unfold Setminus. unfold In. auto.
Qed.

Lemma Setminus_def : forall (U : Type) (A B : Ensemble U),
  A − B = A ⋂ B′.
Proof.
  intros U A B. apply set_equal_def. intros x. split; intros H1.
  - pose proof In_Intersection_def U A (B'). apply In_Intersection_def. apply In_Setminus_def in H1. auto.
  - apply In_Intersection_def in H1. apply In_Setminus_def. auto.
Qed.

Lemma Subset_def : forall (U : Type) (A B : Ensemble U),
  A ⊆ B <-> forall x, x ∈ A -> x ∈ B.
Proof.
  intros U A B. split; intros H1 x H2; apply H1; auto.
Qed.

Lemma not_Subset_def : forall (U : Type) (A B : Ensemble U),
  A ⊈ B <-> exists x, x ∈ A /\ x ∉ B.
Proof.
  intros U A B. split; intros H1.
  - apply not_all_ex_not in H1. destruct H1 as [x H1]. exists x. apply imply_to_and in H1. auto.
  - intros H2. destruct H1 as [x H1]. rewrite Subset_def in H2. apply H1. apply (H2 x). apply H1.
Qed.

Ltac break_union_intersection :=
  repeat match goal with
  | [ H: ?x ∈ _ ⋃ _ |- _] => apply In_Union_def in H
  | [ H: ?x ∈ _ ⋂ _ |- _ ] => apply In_Intersection_def in H
  | [ H: _ /\ _ |- _ ] => destruct H
  | [ H: _ \/ _ |- _ ] => destruct H
  end.

Ltac solve_in_Union :=
  simpl; auto;
  match goal with
  | [ |- ?x ∈ Singleton _ _ ] => 
      apply Singleton_intro; (try reflexivity; try nia; try nra)
  | [ |- ?x ∈ Union _ ?A ?B ] => 
      apply In_Union_def; solve [ left; solve_in_Union | right; solve_in_Union ]
  | [ |- ?G ] => fail "Goal not solvable"
  end.

(*
Ltac solve_in_Union :=
  simpl; auto;
  match goal with
  | [ |- ?x ∈ Singleton _ _ ] => apply Singleton_intro; (try reflexivity; try nia; try nra)
  | [ |- ?x ∈ _ ⋃ _ ] => apply In_Union_def; solve [ left; solve_in_Union | right; solve_in_Union ]
  | [ |- ?G ] => fail "Goal not solvable"
  end.
*)

Ltac solve_in_Intersection :=
  simpl; auto;
  match goal with
  | [ |- ?x ∈ Singleton _ _ ] => apply Singleton_intro; (try reflexivity; try nia; try nra)
  | [ |- ?x ∈ _ ⋂ _ ] => apply In_Intersection_def; split; solve_in_Intersection
  | [ |- ?G ] => fail "Goal not solvable"
  end.

Ltac solve_in_Intersection_Union_helper :=
  intros; break_union_intersection; simpl; auto; (try contradiction);
  match goal with
  | [ |- ?x ∈ ?A \/ ?x ∈ ?A′ ] => apply classic
  | [ |- ?x ∈ Full_set _ ] => apply Full_intro
  | [ |- ?x ∈ Singleton _ _ ] => apply Singleton_intro; (try reflexivity; try nia; try nra)
  | [ |- ?x ∈ _ ⋂ _ ] => apply In_Intersection_def; split; solve_in_Intersection_Union_helper
  | [ |- ?x ∈ _ ⋃ _ ] => apply In_Union_def; (try tauto);  solve [ left; solve_in_Intersection_Union_helper | right; solve_in_Intersection_Union_helper ]
  | [ |- ?G ] => fail "Goal not solvable"
  end.

Ltac solve_in_Intersection_Union := break_union_intersection; solve_in_Intersection_Union_helper.

Ltac solve_set_equality := intros; apply set_equal_def; intros x; split; intros; solve_in_Intersection_Union.

Lemma Union_comm : forall (U : Type) (A B : Ensemble U),
  A ⋃ B = B ⋃ A.
Proof.
  solve_set_equality.
Qed.

Lemma Intersection_comm : forall (U : Type) (A B : Ensemble U),
  A ⋂ B = B ⋂ A.
Proof.
  solve_set_equality.
Qed.

Lemma In_singleton_def : forall (U : Type) (x y : U),
  x ∈ Singleton U y <-> x = y.
Proof.
  intros U x y. split; intros H1.
  - apply Singleton_inv in H1. auto.
  - apply Singleton_intro. auto.
Qed.

Lemma Union_assoc : forall (U : Type) (A B C : Ensemble U),
  A ⋃ (B ⋃ C) = (A ⋃ B) ⋃ C.
Proof.
  solve_set_equality.
Qed.

Lemma Intersection_assoc : forall (U : Type) (A B C : Ensemble U),
  A ⋂ (B ⋂ C) = (A ⋂ B) ⋂ C.
Proof.
  solve_set_equality.
Qed.


Lemma Union_Distrib_Intersection : forall (U : Type) (A B C : Ensemble U),
  A ⋃ (B ⋂ C) = (A ⋃ B) ⋂ (A ⋃ C).
Proof.
  solve_set_equality.
Qed.

Lemma Intersection_Distrib_Union : forall (U : Type) (A B C : Ensemble U),
  A ⋂ (B ⋃ C) = (A ⋂ B) ⋃ (A ⋂ C).
Proof.
  solve_set_equality.
Qed.

Lemma Union_Identity : forall (U : Type) (A : Ensemble U),
  ∅ ⋃ A = A.
Proof.
  solve_set_equality.
Qed.

Lemma Intersection_Identity : forall (U : Type) (A : Ensemble U),
  A ⋂ Full_set U = A.
Proof.
  solve_set_equality.
Qed.

Lemma Union_Complement : forall (U : Type) (A : Ensemble U),
  A′ ⋃ A = Full_set U.
Proof.
  intros U A. apply set_equal_def. intros x. split; intros; break_union_intersection.
  - apply Full_intro.
  - apply Full_intro.
  - apply In_Union_def. tauto.
Qed.

Lemma Intersection_Complement : forall (U : Type) (A : Ensemble U),
  A ⋂ A′ = ∅.
Proof.
  solve_set_equality.
Qed.

Lemma De_Morgan_Union : forall (U : Type) (A B : Ensemble U),
  (A ⋃ B)′ = A′ ⋂ B′.
Proof.
  intros U A B. apply set_equal_def. intros x. split; intros H1.
  - apply In_Intersection_def. apply not_or_and. intros H2. apply H1. apply In_Union_def. auto.
  - apply In_Intersection_def in H1 as [H1 H2]. intros H3. apply In_Union_def in H3 as [H3 | H3]; auto.
Qed.

Lemma De_Morgan_Intersection : forall (U : Type) (A B : Ensemble U),
  (A ⋂ B)′ = A′ ⋃ B′.
Proof.
  intros U A B. apply set_equal_def. intros x. split; intros H1.
  - apply In_Union_def. apply not_and_or. intros H2. apply H1. apply In_Intersection_def. auto.
  - apply In_Union_def in H1. apply or_not_and in H1. intros H2. apply H1. apply In_Intersection_def. auto.
Qed.

Lemma not_in_Union : forall (U : Type) (A B : Ensemble U) (x : U),
  x ∉ A /\ x ∉ B <-> x ∉ A ⋃ B.
Proof.
  intros U A B x. split.
  - intros [H1 H2]. intros H3. apply In_Union_def in H3. tauto.
  - intros H1. split; intros H2; apply H1; apply In_Union_def; auto.
Qed.

Lemma not_in_Intersection : forall (U : Type) (A B : Ensemble U) (x : U),
  x ∉ A \/ x ∉ B <-> x ∉ A ⋂ B.
Proof.
  intros U A B x. split.
  - intros [H1 | H1]; intros H2; apply In_Intersection_def in H2; tauto.
  - intros H1. destruct (In_or_not U A x) as [H2 | H2]; destruct (In_or_not U B x) as [H3 | H3]; auto.
    exfalso. apply H1. apply In_Intersection_def; auto.
Qed.

Lemma not_in_Complement : forall (U : Type) (A : Ensemble U) (x : U),
  x ∉ A <-> x ∈ A′.
Proof.
  intros U A x. split; auto.
Qed.

Lemma not_in_Setminus : forall (U : Type) (A B : Ensemble U) (x : U),
  x ∉ A − B <-> x ∉ A \/ x ∈ B.
Proof.
  intros U A B x. split.
  - intros H1. destruct (In_or_not U B x) as [H2 | H2]; auto. left. intros H3. apply H1. apply In_Setminus_def. auto.
  - intros [H1 | H1] H2.
    -- apply H1. apply In_Setminus_def in H2 as [H2 H3]. auto.
    -- apply In_Setminus_def in H2 as [H2 H3]. auto.
Qed.

Lemma Complement_Complement : forall (U : Type) (A : Ensemble U),
  A′′ = A.
Proof.
  intros U A. apply set_equal_def. intros x. split; intros H1.
  - pose proof In_or_not U A x as [H2 | H2]; auto. exfalso. apply H1. apply H2.
  - intros H2. apply H2. auto.
Qed.

Lemma Setminus_Complement : forall (U : Type) (A B : Ensemble U),
  (A − B)′ = A′ ⋃ B.
Proof.
  intros U A B. rewrite Setminus_def. rewrite De_Morgan_Intersection. rewrite Complement_Complement. reflexivity.
Qed.

Ltac destruct_finite_sets H :=
  match type of H with
  | ?x ∈ ⦃⦄ => inversion H
  | ?x ∈ ⦃_⦄ => apply In_singleton_def in H
  | ?x ∈ _  => 
      apply In_Union_def in H as [H | H];
      [ apply In_singleton_def in H
      | destruct_finite_sets H]
  end.

Ltac destruct_all_finitesets :=
  repeat match goal with
  | [ H : ?x ∈ _ |- _ ] => try (destruct_finite_sets H; inversion H; solve_R)
  end.

Ltac break_union_intersection_2 :=
  repeat match goal with
  | [ H: ?x ∈ _ ⋃ _ |- _ ] => apply In_Union_def in H
  | [ H: ?x ∈ _ ⋂ _ |- _ ] => apply In_Intersection_def in H 
  | [ H: _ /\ _ |- _ ] => destruct H
  | [ H: _ \/ _ |- _ ] => destruct H
  | [ H: ?x ∈ (?A ⋃ ?B)′ |- _ ] => rewrite De_Morgan_Union in H
  | [ H: ?x ∈ (?A ⋂ ?B)′ |- _ ] => rewrite De_Morgan_Intersection in H
  | [ H: ?x ∈ (?A − ?B)′ |- _ ] => rewrite Setminus_Complement in H
  | [ H: ?x ∈ _ − _ |- _ ] => rewrite In_Setminus_def in H
  | [ H: ?x ∉ _ ⋃ _ |- _ ] => rewrite not_in_Union in H
  | [ H: ?x ∉ _ ⋂ _ |- _ ] => rewrite not_in_Intersection in H
  | [ H: ?x ∉ _ |- _ ] => rewrite not_in_Complement in H
  | [ H: ?x ∉ _ − _ |- _ ] => rewrite not_in_Setminus in H
  | [ H: _ = _ |- _ ] => injection H; intros; subst; clear H
  end.

Ltac solve_in_Intersection_Union_helper_2 :=
  subst; unfold list_to_ensemble in *; intros; break_union_intersection_2; simpl; auto; (try contradiction);
  match goal with
  | [ |- ?x ∉ _ ⋃ _ ] => apply not_in_Union; split; solve_in_Intersection_Union_helper_2
  | [ |- ?x ∉ _ ⋂ _ ] => apply not_in_Intersection; (try tauto); solve [ left; solve_in_Intersection_Union_helper_2 | right; solve_in_Intersection_Union_helper_2 ]
  | [ |- ?x ∉ _ − _ ] => rewrite not_in_Setminus; solve_in_Intersection_Union_helper_2
  | [ |- ?x ∉ _ ] => rewrite not_in_Complement; solve_in_Intersection_Union_helper_2 
  | [ |- ?x ∈ Full_set _ ] => apply Full_intro
  | [ |- ?x ∈ Singleton _ _ ] => apply Singleton_intro; (try reflexivity; try nia; try nra)
  | [ |- ?x ∈ _ − _] => try (apply In_Setminus_def); split; solve_in_Intersection_Union_helper_2
  | [ |- ?x ∈ (_ ⋂ _)′ ] => rewrite De_Morgan_Intersection; solve_in_Intersection_Union_helper_2
  | [ |- ?x ∈ (_ ⋃ _)′ ] => rewrite De_Morgan_Union; solve_in_Intersection_Union_helper_2
  | [ |- ?x ∈ (_ − _)′ ] => rewrite Setminus_Complement; solve_in_Intersection_Union_helper_2
  | [ |- ?x ∈ (_)′′ ] => rewrite Complement_Complement; solve_in_Intersection_Union_helper_2
  | [ |- ?x ∈ _ ⋂ _ ] => apply In_Intersection_def; split; solve_in_Intersection_Union_helper_2
  | [ |- ?x ∈ _ ] => apply In_Union_def; (try tauto); solve [ left; solve_in_Intersection_Union_helper_2 | right; solve_in_Intersection_Union_helper_2 ]
  | [ |- ?G ] => fail "Goal not solvable"
  end.

Ltac in_list x l :=
  match l with
  | context[x] => constr:(true)
  | _ => constr:(false)
  end.

Ltac find_sets_in_expr E acc :=
  match E with
  | ?A ⋃ ?B =>
      let acc' := find_sets_in_expr A acc in
      find_sets_in_expr B acc'
  | ?A ⋂ ?B =>
      let acc' := find_sets_in_expr A acc in
      find_sets_in_expr B acc'
  | ?A − ?B =>
      let acc' := find_sets_in_expr A acc in
      find_sets_in_expr B acc'
  | ?A′ => find_sets_in_expr A acc
  | ?A =>
      let is_in := in_list A acc in
      match is_in with
      | true => acc (* Do nothing, A is already in the list *)
      | false => constr:(A :: acc) (* Add A to the accumulator *)
      end
  end.

Ltac get_U_from_expr E :=
  match type of E with
  | Ensemble ?U => constr:(U)
  | _ => fail "Cannot find U in" E
  end.

Ltac find_sets_in_goal U :=
  match goal with
  | |- ?x ∈ ?LHS <-> ?x ∈ ?RHS =>
      let acc := constr:(@nil (Ensemble U)) in
      let L := find_sets_in_expr LHS acc in
      find_sets_in_expr RHS L
  end.

Ltac pose_in_or_not_for_sets x :=
  let U := type of x in
  let sets := find_sets_in_goal U in
  let rec process_sets s :=
    match s with
    | nil => idtac
    | cons ?A ?xs =>
        pose proof (In_or_not U A x);
        process_sets xs
    end
  in
  process_sets sets.

Ltac solve_set_equality_auto :=
  intros; apply set_equal_def; let x := fresh "x" in intros x; pose_in_or_not_for_sets x; 
  split; intros; destruct_all_finitesets; solve_in_Intersection_Union_helper_2.

Ltac solve_set_equality_auto' :=
  intros; apply set_equal_def; let x := fresh "x" in intros x; split; intros; 
  destruct_all_finitesets; solve_in_Intersection_Union_helper_2.

Lemma De_Morgan_Intersection_2 : forall (U : Type) (A B : Ensemble U),
  A = A.
Proof.
  solve_set_equality_auto.
Qed.

Lemma testinggg : forall (U : Type) (A B : Ensemble U),
  (A − B)′ = A′ ⋃ B.
Proof.
  solve_set_equality_auto.
Qed.

Lemma set_mins_tester : forall (U : Type) (A B C : Ensemble U),
   (A − (B ⋃ C)) = (A ⋂ (B′ ⋂ C′)).
Proof.
  solve_set_equality_auto.
Qed.

Lemma set_difference_union : forall (U : Type) (A B C : Ensemble U),
  (A − B) ⋃ (B − C) = (A ⋃ B) − (B ⋂ C).
Proof.
  solve_set_equality_auto.
Qed.

Lemma complex_set_lemma :
  forall (U : Type) (A B C : Ensemble U),
    ((A ⋂ (B ⋃ C)) ⋂ (A − B)) ⋂ (B ⋂ C′) = ∅.
Proof.
  solve_set_equality_auto.
Qed.

Ltac solve_not_in_ensemble :=
  simpl;
  match goal with
  | [ |- ?x ∉ ∅ ] => intros H_69420; inversion H_69420
  | [ |- ?x ∉ Singleton _ _ ] => intros H_69420; apply Singleton_inv in H_69420; (try inversion H_69420; try nia; try nra)
  | [ |- ?x ∉ _ ⋃ _ ] => apply not_in_Union; split; solve_not_in_ensemble
  | [ |- ?x ∉ _ ⋂ _ ] => apply not_in_Intersection; (try tauto); solve [ left; solve_not_in_ensemble | right; solve_not_in_ensemble ]
  | [ |- ?G ] => fail "Goal not solvable"
  end.

Ltac autoset :=
  subst;
  try (solve_set_equality_auto'); try (solve_set_equality_auto); try (solve_in_Union); try (solve_not_in_ensemble); try (solve_in_Intersection_Union_helper_2).

Fixpoint Union_f_n {A : Type} (f : nat -> Ensemble A) (n : nat) : Ensemble A :=
  match n with
  | 0 => f 0
  | S n' =>  Union_f_n f n' ⋃ f n
  end.

Lemma Union_f_n_S : forall (A : Type) (f : nat -> Ensemble A) (n : nat),
  Union_f_n f (S n) = Union_f_n f n ⋃ f (S n).
Proof.
  intros A f n. simpl. apply set_equal_def. intros x. split; intros H1.
  - apply In_Union_def in H1. destruct H1 as [H1 | H1].
    -- apply In_Union_def. left. auto.
    -- apply In_Union_def. right. auto.
  - apply In_Union_def in H1. destruct H1 as [H1 | H1].
    -- apply In_Union_def. left. auto.
    -- apply In_Union_def. right. auto.
Qed.

Lemma list_to_ensemble_not_empty : forall (U : Type) (l : list U),
  l ≠ nil <-> list_to_ensemble l ≠ ∅.
Proof.
  intros U l. split.
  - intros H1. destruct l as [| h t] eqn : El; try contradiction. intros H2. rewrite list_to_ensemble_cons in H2.
    rewrite set_equal_def in H2. specialize (H2 h) as [H2 _]. assert (h ∈ Singleton U h) as H3.
    { apply In_singleton. } rewrite In_Union_def in H2. assert (h ∈ ∅) as H4. { apply H2. auto. } contradiction.
  - intros H1. destruct l as [| h t] eqn : El; try contradiction. intros H2. inversion H2.
Qed.

Lemma list_to_ensemble_nil : forall (U : Type),
  list_to_ensemble (@nil U) = ∅.
Proof.
  intros U. simpl. reflexivity.
Qed.

Lemma list_to_ensemble_not_empty_exists : forall (U : Type) (l : list U),
  l ≠ nil <-> exists x, x ∈ list_to_ensemble l.
Proof.
  intros U l. split.
  - intros H1. destruct l as [| h t]; try contradiction.
    exists h. rewrite list_to_ensemble_cons. autoset.
  - intros [x H1] H2. destruct l as [| h t]; [ autoset | inversion H2].
Qed.

Lemma list_to_ensemble_map_not_empty : forall (U V : Type) (l : list U) (f : U -> V),
  l ≠ nil -> list_to_ensemble (map f l) ≠ ∅.
Proof.
  intros U V l f H1. apply list_to_ensemble_not_empty. intros H2. apply H1. apply map_eq_nil in H2. auto.
Qed.

Lemma In_list_to_ensemble : forall (U : Type) (l : list U) (x : U),
  List.In x l <-> x ∈ list_to_ensemble l.
Proof.
  intros U l x. split.
  - intros H1. induction l as [| h t IH].
    -- inversion H1.
    -- simpl. destruct H1 as [H1 | H1].
      ++ rewrite H1. apply In_Union_def. left. apply In_singleton.
      ++ specialize (IH H1). apply In_Union_def. right. auto.
  - intros H1. induction l as [| h t IH].
    -- inversion H1.
    -- simpl in H1. apply In_Union_def in H1. destruct H1 as [H1 | H1].
      ++ simpl. left. apply Singleton_inv in H1. auto.
      ++ right. apply IH. auto.
Qed.

Lemma list_eq_In : forall (U : Type) (l1 l2 : list U),
  l1 = l2 -> (forall x, List.In x l1 -> List.In x l2).
Proof.
  intros U l1 l2 H1 x H2. generalize dependent l2. induction l1 as [| h t IH].
  - inversion H2.
  - intros l2 H3. simpl in H2. destruct H2 as [H2 | H2].
    -- rewrite H2 in H3. destruct l2 as [| h' t'] eqn : El2.
      ++ inversion H3.
      ++ inversion H3. left. auto.
    -- assert (x = h \/ x <> h) as [H4 | H4] by apply classic.
       ++ inversion H3. left. auto.
       ++ inversion H3. right. auto.
Qed.

Lemma list_to_ensemble_eq_iff : forall (U : Type) (l1 l2 : list U),
  list_to_ensemble l1 = list_to_ensemble l2 <-> forall x, List.In x l1 <-> List.In x l2.
Proof.
  intros U l1 l2. split.
  - intros H1. rewrite set_equal_def in H1. intros x. specialize (H1 x) as [H1 H2]. split.
    -- intros H3. apply In_list_to_ensemble. apply H1. apply In_list_to_ensemble in H3. auto.
    -- intros H3. apply In_list_to_ensemble. apply In_list_to_ensemble in H3. auto.
  - intros H1. apply set_equal_def. intros x. split; intros H2.
    -- apply In_list_to_ensemble in H2. apply In_list_to_ensemble. apply H1; auto.
    -- apply In_list_to_ensemble in H2. apply In_list_to_ensemble. apply H1; auto.
Qed.

Lemma Finite_set_iff_Finite_set' : forall (U : Type) (A : Ensemble U),
  Finite_set A <-> Finite_set' A.
Proof.
  intros U A. split; intros [l H1].
  - pose proof (exists_no_Dup _ l) as [l' [H2 H3]]. exists l'. split; auto.
    rewrite <- H1. apply list_to_ensemble_eq_iff. intros x. specialize (H3 x). tauto.
  - exists l. tauto.
Qed.

Lemma In_Power_set_def : forall (U : Type) (A B : Ensemble U),
  B ∈ ℙ(A) <-> B ⊆ A.
Proof.
  intros U A B. split; intros H1.
  - unfold In, Power_set in H1. auto.
  - unfold In, Power_set. auto.
Qed.

Lemma Power_Set_equiv_Power_set : forall {U : Type} (A B : Ensemble U),
  B ∈ ℙ(A) <->  B ∈ (Powerset.Power_set U A).
Proof.
  intros U A B. split; intros H1.
  - rewrite In_Power_set_def in H1. constructor. auto.
  - rewrite In_Power_set_def. destruct H1 as [X H1]. auto.
Qed.

Lemma Finite_set_equiv_Finite : forall (U : Type) (A : Ensemble U),
  Finite_set A <-> Finite_sets.Finite U A.
Proof.
  intros U A. split.
  - intros [l H1]. generalize dependent A. induction l as [| h t IH].
    -- intros A H1. rewrite list_to_ensemble_nil in H1. rewrite <- H1. apply Empty_is_finite.
    -- intros A H1. rewrite list_to_ensemble_cons in H1. rewrite <- H1. destruct (classic (h ∈ list_to_ensemble t)) as [H2 | H2].
      + assert (⦃h⦄ ⋃ list_to_ensemble t = list_to_ensemble t) as H3.
        {
           apply set_equal_def. intros x. split; intros H3; try autoset.
           apply In_Union_def in H3 as [H3 | H3]; auto. apply In_singleton_def in H3. rewrite H3. apply H2.
        }
        rewrite H3 in H1. rewrite H3. specialize (IH A). rewrite <- H1 in IH at 2. specialize (IH H1). auto.
      + replace (⦃h⦄ ⋃ list_to_ensemble t) with (Add _ (list_to_ensemble t) h). 2 : { unfold Add; autoset. }
        apply Union_is_finite; auto.
  - intros H1. induction H1 as [| A H1 IH].
    -- exists []. rewrite list_to_ensemble_nil. reflexivity.
    -- destruct IH as [l H2]. unfold Finite_set. exists (x :: l). unfold Add. rewrite <- H2. autoset.
Qed.

Lemma not_in_minus_eq : forall (U : Type) (A : Ensemble U) (x : U),
  x ∉ A -> A − ⦃x⦄ = A.
Proof.
  intros U A x H1. apply set_equal_def. intros y. split; intros H2; autoset.
  apply In_Setminus_def. split. autoset. intros H3. apply In_singleton_def in H3. autoset.
Qed.

Lemma In_set_Union_eq : forall (U : Type) (A : Ensemble U) (x : U),
  x ∈ A -> A = A ⋃ ⦃x⦄.
Proof.
  intros U A x H1. apply set_equal_def. intros y. split; intros H2; autoset.
  apply In_Union_def in H2 as [H2 | H2]; autoset. apply In_singleton_def in H2. autoset.
Qed.

Lemma Intersection_preserves_finite_2 : forall (U : Type) (A B : Ensemble U),
  Finite_set A -> Finite_set (A ⋂ B).
Proof.
  intros U A B [l H1]. unfold Finite_set. generalize dependent A. induction l as [| h t IH].
  - intros A H1. rewrite list_to_ensemble_nil in H1. exists []; autoset.
  - intros A H1. rewrite list_to_ensemble_cons in H1. pose proof (classic (h ∈ (list_to_ensemble t))) as [H2 | H2].
    -- assert (list_to_ensemble t = A) as H3. { apply In_set_Union_eq in H2. rewrite H2. autoset. }
       specialize (IH A H3). destruct IH as [l H4]. exists l. autoset.
    -- assert (list_to_ensemble t = A − ⦃h⦄) as H3. { apply set_equal_def. intros x. split; intros H3; autoset. 
            apply In_Setminus_def. split. autoset. intros H4. apply H2. apply In_singleton_def in H4. autoset. }
       specialize (IH (A − ⦃h⦄) H3) as [l H4]. pose proof (In_or_not U B h) as [H5 | H5].
       * pose proof (In_or_not U A h) as [H6 | H6].
         ++ exists (h :: l). rewrite list_to_ensemble_cons. rewrite H4. rewrite Union_Distrib_Intersection. 
            replace (⦃h⦄ ⋃ (A − ⦃h⦄)) with A. 2 : { autoset. } replace (⦃h⦄ ⋃ B) with (B). 2 : { rewrite Union_comm. apply In_set_Union_eq. autoset. } autoset.
         ++ exists l. rewrite not_in_minus_eq in H4; auto.
       * exists l. rewrite H4. apply set_equal_def. intros x. split; intros H6. autoset. apply In_Intersection_def. split. 2 : { autoset. }
         apply In_Setminus_def. split. autoset. intros H7. apply H5. apply In_Intersection_def in H6. apply In_singleton_def in H7. autoset.
Qed.

Lemma Subset_Empty_def : forall (U : Type) (A : Ensemble U),
  A ⊆ ∅ <-> A = ∅.
Proof.
  intros U A. split; intros H1.
  - apply set_equal_def. intros x. split; intros H2.
    -- apply H1 in H2; auto.
    -- contradiction.
  - rewrite H1. apply Subset_refl.
Qed.

Lemma Empty_or_exists_In : forall (U : Type) (A : Ensemble U),
  A = ∅ \/ exists x : U, x ∈ A.
Proof.
  intros U A. destruct (classic (A = ∅)) as [H1 | H1]; auto; right.
  apply NNPP. intros H2. apply H1. apply set_equal_def. intros x; split; intro H3.
  - exfalso. apply H2. exists x. auto.
  - contradiction.
Qed.

Lemma Infinite_exists_In : forall (U : Type) (A : Ensemble U),
  ~Finite_set A -> exists x : U, x ∈ A.
Proof.
  intros U A H1. pose proof Empty_or_exists_In U A as [H2 | H2]; auto.
  exfalso. apply H1. exists []. autoset.
Qed.

Lemma Power_set_Empty_1 : forall (U : Type),
  ℙ(∅ : Ensemble U) = Singleton (Ensemble U) (Empty_set _).
Proof.
  intros U. apply set_equal_def; intros x; split; intros H1. 
  - rewrite In_Power_set_def in H1. rewrite Subset_def in H1. pose proof (Empty_or_exists_In U x) as [H2 | [y H2]].
    -- rewrite H2. solve_in_Union.
    -- specialize (H1 y H2). contradiction.
  - rewrite In_Power_set_def. rewrite Subset_def. intros y H2. apply In_singleton_def in H1. rewrite H1 in H2. apply H2.
Qed.

Lemma Power_set_Empty_2 : forall (U : Type) (A : Ensemble U),
  ℙ(A) = ⦃⦃⦄⦄ <-> A = ∅.
Proof.
  intros U A. split; intros H1.
  - rewrite set_equal_def in H1. apply set_equal_def. intros x. split; intros H2.
    -- specialize (H1 A) as [H1 H3]. rewrite In_Power_set_def in H1. specialize (H1 (Subset_refl U A)). apply In_singleton_def in H1. autoset.
    -- contradiction.
  - rewrite H1. apply Power_set_Empty_1.
Qed.

Lemma Empty_In_Power_set : forall (U : Type) (A : Ensemble U),
  ∅ ∈ ℙ(A).
Proof.
  intros U A. rewrite In_Power_set_def. apply Empty_Subset.
Qed.

Section PowerSetBuilder.
  Fixpoint remove_duplicates_aux {U : Type} (eq_dec : forall x y, { x = y } + { x ≠ y }) (l acc : list U) : list U :=
    match l with
    | [] => rev acc
    | x :: xs =>
        if in_dec eq_dec x acc then
          remove_duplicates_aux eq_dec xs acc
        else
          remove_duplicates_aux eq_dec xs (x :: acc)
    end.

  Definition remove_duplicates {U : Type} (eq_dec : forall x y, { x = y } + { x ≠ y }) (l : list U) : list U :=
    remove_duplicates_aux eq_dec l [].

  Fixpoint PowerSetBuilder_aux {U : Type} (l : list U) : list (list U) :=
    match l with
    | [] => [[]]
    | x :: xs =>
        let ps := PowerSetBuilder_aux xs in
        ps ++ map (fun s => x :: s) ps
    end.

  Definition PowerSetBuilder {U : Type} (eq_dec : forall x y, { x = y } + { x ≠ y }) (l : list U) : Ensemble (Ensemble U) :=
    let l' := remove_duplicates eq_dec l in list_to_ensemble (map list_to_ensemble (PowerSetBuilder_aux l')).

End PowerSetBuilder.

Lemma cardinal_Empty_1 : forall (U : Type) (A : Ensemble U),
  cardinal U (A) 0 <-> A = ∅.
Proof.
  intros U A. split; intros H1.
  - apply cardinal_invert in H1; auto.
  - rewrite H1. apply card_empty.
Qed.

Lemma cardinal_Empty_2 : forall (U : Type) (n : nat),
  ‖(∅ : Ensemble U)‖ = n -> n = 0.
Proof.
  intros U n H1. destruct n as [| n]; auto. exfalso. apply cardinal_invert in H1 as [A [x [H1 [H2 H3]]]].
  rewrite set_equal_def in H1. specialize (H1 x) as [H1 H4]. unfold Add in H4. assert (x ∈ A ⋃ ⦃x⦄) as H5.
  { apply In_Union_def. right. apply In_singleton_def. auto. } specialize (H4 H5). contradiction.
Qed.

Lemma cardinal_Singleton : forall (U : Type) (x : U),
  ‖⦃x⦄‖ = 1.
Proof.
  intros U x. replace (Singleton U x) with (∅ ⋃ Singleton U x) by autoset. apply card_add; [apply card_empty | autoset].
Qed.

Lemma cardinal_inifinite : forall (U : Type) (A : Ensemble U),
  ~Finite U A -> forall n : nat, ~ ‖A‖ = n.
Proof.
  intros U A H1 n H2. generalize dependent A. induction n as [| k IH].
  - intros A H1 H2. apply cardinal_invert in H2. apply H1. rewrite H2. apply Empty_is_finite.
  - intros A H1 H2. apply H1. apply cardinal_invert in H2 as [B [x [H2 [H3 H4]]]]. rewrite H2. apply Union_is_finite; auto.
    destruct k as [| k'].
    -- inversion H4. apply Empty_is_finite.
    -- exfalso. apply (IH B); auto. intros H5. apply H1. rewrite H2. apply Union_is_finite; auto.
Qed.

Lemma cardinal_minus : forall (U : Type) (A : Ensemble U) (h : U) (n : nat),
  ‖A‖ = S n -> h ∈ A -> ‖A − ⦃h⦄‖ = n.
Proof.
  intros U A h n H1 H2. replace (A − ⦃h⦄) with (Subtract U A h) by autoset.
  replace n with (Nat.pred (S n)) by lia.
  apply card_soustr_1; auto.
Qed.

Lemma In_Im_def : forall (U V : Type) (A : Ensemble U) (f : U -> V) (y : V),
  y ∈ Im U V A f <-> exists x : U, x ∈ A /\ f x = y.
Proof.
  intros U V A f y. split; intros H1.
  - apply Im_inv in H1. auto.
  - destruct H1 as [x [H1 H2]]. apply Im_intro with (x := x); auto.
Qed.

Lemma Power_set_Add :
  forall (U : Type) (A : Ensemble U) (h : U),
    Power_set (Add U A h) =
    Union (Ensemble U)
      (Power_set A)
      (Im (Ensemble U) (Ensemble U) (Power_set A) (fun S => Add U S h)).
Proof.
  intros U A h. apply set_equal_def. intros x. split; intros H1.
  - rewrite In_Power_set_def in H1. rewrite In_Union_def. destruct (classic (h ∈ x)) as [H2 | H2].
    -- right. rewrite In_Im_def. exists (x − ⦃h⦄). split.
       * unfold Add in H1. apply In_Power_set_def. apply Subset_def. intros y H3. apply In_Setminus_def in H3 as [H3 H4].
         rewrite Subset_def in H1. specialize (H1 y H3). autoset.
       * unfold Add in *. rewrite Subset_def in H1. apply set_equal_def. intros y. split; intros H3.
         + specialize (H1 y). apply In_Union_def in H3 as [H3 | H3]; try autoset. apply In_singleton_def in H3. autoset.
         + apply In_Union_def. destruct (classic (y = h)) as [H4 | H4]. right. apply In_singleton_def; auto. left. apply In_Setminus_def. split; autoset.
    -- left. apply In_Power_set_def. apply Subset_def. intros y H3. rewrite Subset_def in H1. specialize (H1 y H3). unfold Add in H1. 
       apply In_Union_def in H1 as [H1 | H1]; autoset. apply In_singleton_def in H1. subst. contradiction.
  - rewrite In_Power_set_def. apply In_Union_def in H1 as [H1 | H1].
    -- unfold Add. apply Subset_def. intros y H2. rewrite In_Power_set_def in H1. autoset.
    -- rewrite In_Im_def in H1. destruct H1 as [S [H1 H2]]. unfold Add in *. rewrite In_Power_set_def in H1. rewrite set_equal_def in H2. 
       apply Subset_def. intros y H3. specialize (H2 y). destruct H2 as [H2 H4]. specialize (H4 H3). autoset.
Qed.

Lemma Add_Union_assoc : forall (U : Type) (A B : Ensemble U) (h : U),
  Add U (A ⋃ B) h = (Add U A h) ⋃ B.
Proof.
  unfold Add. autoset.
Qed.

Lemma cardinal_Union : forall (U : Type) (A B : Ensemble U) (n m : nat),
  ‖A‖ = n -> ‖B‖ = m -> A ⋂ B = ∅ -> ‖A ⋃ B‖ = n + m.
Proof.
  intros U A B n m H1 H2 H3. induction H1 as [| A n H1 IH x H4].
  - rewrite Union_Identity. simpl. auto.
  - assert (H5 : A ⋂ B = ∅). { rewrite <- H3. unfold Add in *. apply set_equal_def. intros y. split; intros H5; autoset. rewrite H3 in H5. contradiction. }
    specialize (IH H5). rewrite <- Add_Union_assoc. apply card_add; auto. intros H6. apply H4. unfold Add in *. apply In_Union_def in H6 as [H6 | H6]; autoset.
    rewrite set_equal_def in H3. specialize (H3 x) as [H3 H7]. assert (x ∈ (A ⋃ ⦃x⦄) ⋂ B) as H8 by autoset. specialize (H3 H8). contradiction. 
Qed.

Lemma h_not_in_Power_set_A : forall (U : Type) (A : Ensemble U) (h : U),
  h ∉ A -> forall x, x ∈ ℙ(A) -> h ∉ x.
Proof.
  intros U A h H1 x H2. rewrite In_Power_set_def in H2. autoset.
Qed.

Lemma Add_not_in_preserves_cardinality : forall (U : Type) (A : Ensemble (Ensemble U)) (h : U) (n : nat),
  (forall x, x ∈ A -> h ∉ x) -> ‖A‖ = n -> ‖(Im (Ensemble U) (Ensemble U) A (fun S : Ensemble U => Add U S h))‖ = n.
Proof.
  intros U A h n H1 H2. induction H2 as [| A n H2 IH x H3].
  - rewrite image_empty. apply card_empty.
  - rewrite Im_add. apply card_add; auto. apply IH. intros y H4. apply H1. unfold Add. autoset.
    intros H4. apply In_Im_def in H4 as [S [H4 H5]]. specialize (H1 S) as H6. assert (S ∈ Add (Ensemble U) A x) as H7. { unfold Add. autoset. }
    specialize (H6 H7). clear H7. specialize (H1 x). assert (x ∈ Add (Ensemble U) A x) as H7. { unfold Add. autoset. }
    specialize (H1 H7). clear H7. destruct Empty_or_exists_In with (U := U) (A := S) as [H7 | [y H7]]; destruct Empty_or_exists_In with (U := U) (A := x) as [H8 | [z H8]]; autoset.
    -- rewrite set_equal_def in H5. specialize (H5 z) as [H5 H9]. assert (H10 : z ∈ Add U x h) by (unfold Add; autoset). specialize (H9 H10). unfold Add in H9.
       rewrite Union_Identity in H9. apply In_singleton_def in H9. autoset.
    -- rewrite set_equal_def in H5. specialize (H5 y) as [H5 H9]. assert (H10 : y ∈ Add U S h) by (unfold Add; autoset). specialize (H5 H10). unfold Add in H5.
       rewrite Union_Identity in H5. apply In_singleton_def in H5. autoset.
    -- destruct (classic (x = S)) as [H9 | H9]; autoset. apply H9. unfold Add in H5. rewrite set_equal_def in H5. apply set_equal_def. intros w; split; intros H10.
       specialize (H5 w) as [H5 H11].  assert (H12 : w ∈ Add U x h) by (unfold Add; autoset). specialize (H11 H12). apply In_Union_def in H11 as [H11 | H11]; autoset.
       apply In_singleton_def in H11. subst. contradiction. specialize (H5 w) as [H5 H11]. assert (H12 : w ∈ Add U S h) by (unfold Add; autoset). specialize (H5 H12).
       apply In_Union_def in H5 as [H5 | H5]; autoset. apply In_singleton_def in H5. subst. contradiction. 
Qed.

Lemma Power_set_Image_Add_preserves_cardinality : forall (U : Type) (A : Ensemble U) (n : nat) (h : U),
  h ∉ A -> ‖ℙ(A)‖ = n -> ‖Im (Ensemble U) (Ensemble U) (ℙ(A)) (fun S : Ensemble U => Add U S h)‖ = n.
Proof.
  intros U A n h H1 H2. apply Add_not_in_preserves_cardinality. apply h_not_in_Power_set_A; auto. auto.
Qed.

Lemma cardinal_Power_set_add : forall (U : Type) (A : Ensemble U) (h : U) (n : nat),
  ‖ℙ(A)‖ = n -> h ∉ A -> ‖ℙ(Add U A h)‖ = 2 * n.
Proof.
  intros U A h n H1 H2. rewrite Power_set_Add. apply cardinal_Union; auto. rewrite Nat.add_0_r. apply Power_set_Image_Add_preserves_cardinality; auto.
  apply set_equal_def. intros x. split; intros H3; autoset. apply In_Intersection_def in H3 as [H3 H4]; autoset. rewrite In_Power_set_def in H3.
  apply In_Im_def in H4 as [S [H4 H5]]. rewrite In_Power_set_def in H4. unfold Add in H5. autoset. rewrite Subset_def in H4, H3. specialize (H4 h). specialize (H3 h).
  assert (H5 : h ∈ S ⋃ ⦃h⦄) by autoset. specialize (H3 H5). contradiction.
Qed.

Proposition prop_14_6 : forall (U : Type) (A : Ensemble U) (n : nat),
  Finite_set A -> ‖A‖ = n -> ‖ℙ(A)‖ = 2^n.
Proof.
  intros U A n [l H1] H2. generalize dependent A. generalize dependent n. induction l as [| h t IH].
  - intros n A H1 H2. rewrite list_to_ensemble_nil in H1. rewrite <- H1 in H2.
    apply cardinal_Empty in H2. subst. simpl. rewrite Power_set_Empty_1. apply cardinal_Singleton.
  - intros n A H1 H2. rewrite list_to_ensemble_cons in H1. rewrite <- H1 in H2.
    destruct (classic (h ∈ list_to_ensemble t)) as [H3 | H3].
    -- assert (Add _ (list_to_ensemble t) h = list_to_ensemble t) as H4.
       {
          apply set_equal_def. intros x. unfold Add. split; intros H4; try autoset.
          apply In_Union_def in H4 as [H4 | H4]; auto. apply In_singleton_def in H4. autoset.
       }
       rewrite H1 in H2. apply IH; auto. rewrite <- H1. unfold Add in H4. rewrite Union_comm in H4. autoset.
    -- assert (cardinal (Ensemble U) (Power_set (list_to_ensemble t)) (2 ^ (n-1))) as H4.
       {
          apply IH; auto. replace (list_to_ensemble t) with (A − ⦃h⦄). 
          2 : { apply set_equal_def. intros x. rewrite <- H1. split; intros H4. try autoset. apply In_Setminus_def. split; repeat autoset. }
          apply cardinal_minus; autoset. destruct n as [| n']. apply cardinal_Empty_1 in H2. rewrite set_equal_def in H2. specialize (H2 h) as [H2 H5].
          assert (H6 : h ∈ ⦃h⦄ ⋃ list_to_ensemble t) by autoset. specialize (H2 H6). contradiction.
          replace (S (S n' - 1)) with (S n') by lia. auto.
        }
        replace (⦃h⦄ ⋃ list_to_ensemble t) with (Add _ (list_to_ensemble t) h) in H2. 2 : {  unfold Add; autoset. }
        assert (H5 : cardinal (Ensemble U) (Power_set (Add U (list_to_ensemble t) h)) (2 * (2 ^ (n - 1)))).
        { apply cardinal_Power_set_add; auto. } assert (H6 : Add U (list_to_ensemble t) h = A). { rewrite <- H1. unfold Add. autoset. }
        assert (n = 0 \/ n > 0) as [H7 | H7] by lia.
        + subst. apply cardinal_Empty_1 in H2. rewrite set_equal_def in H2. specialize (H2 h) as [H1 H2].
          assert (H7 : h ∈ Add U (list_to_ensemble t) h). { unfold Add. autoset. } specialize (H1 H7). contradiction.
        + rewrite H6 in H5. replace (2 * (2 ^ (n - 1))) with (2 ^ n) in H5. 2 : { replace n with (S (n - 1)) at 1 by lia. rewrite Nat.pow_succ_r'. lia. }
          auto. 
Qed.

Section num_subsets.
  Variable U : Type.

  Definition Subsets_of_Cardinality (A : Ensemble U) (k : nat) : Ensemble (Ensemble U) :=
    fun B => (B ⊆ A)%set /\ ‖B‖ = k.

  Definition Subsets_without_x (A : Ensemble U) (x : U) (k : nat) : Ensemble (Ensemble U) :=
    fun B => (B ⊆ A)%set /\ ~ In _ B x /\ ‖B‖ = k.

  Definition Subsets_with_x (A : Ensemble U) (x : U) (k : nat) : Ensemble (Ensemble U) :=
    fun B => (B ⊆ A)%set /\ In _ B x /\ ‖B‖ = k.

  Lemma Union_of_Subsets : forall (A : Ensemble U) (k : nat) (x : U),
    x ∈ A -> Subsets_of_Cardinality A k = Subsets_without_x A x k ⋃ Subsets_with_x A x k.
  Proof.
    intros A k x H1. apply set_equal_def. intros y. split; intros H2.
    - unfold Subsets_of_Cardinality, In in H2. destruct H2 as [H2 H3]. apply In_Union_def. unfold Subsets_without_x, Subsets_with_x, In.
      pose proof In_or_not U y x as [H4 | H4]; autoset.
    - apply In_Union_def in H2 as [H2 | H2].
      -- unfold Subsets_without_x, In in H2. destruct H2 as [H2 H3]. unfold Subsets_of_Cardinality, In. autoset.
      -- unfold Subsets_with_x, In in H2. destruct H2 as [H2 H3]. unfold Subsets_of_Cardinality, In. autoset.
  Qed.

  Theorem theorem_16_6 : forall (A : Ensemble U) (n k : nat),
    ‖A‖ = n -> ‖Subsets_of_Cardinality A k‖ = choose n k.
  Proof.
    intros A n k H1. generalize dependent k. generalize dependent A. induction n as [| m IH].
    - intros A H1 k. rewrite cardinal_Empty_1 in H1. rewrite H1. destruct (classic (k = 0)) as [H2 | H2].
      -- rewrite H2. replace (Subsets_of_Cardinality ⦃⦄ 0) with (⦃⦃⦄⦄ : Ensemble (Ensemble U)).
         2 : { apply set_equal_def. intros x. split; intro H3. apply In_singleton_def in H3. rewrite H3. constructor. apply Subset_refl. apply card_empty.
               inversion H3. apply cardinal_Empty_1 in H0. autoset. }
         rewrite n_choose_0. apply cardinal_Singleton.
      -- rewrite O_choose_n; auto. apply cardinal_Empty_1. apply set_equal_def. intros x. split; intro H3.
         inversion H3. rewrite Subset_def in H. pose proof (Empty_or_exists_In U x) as [H4 | H4]; auto. rewrite H4 in H0. 
         apply cardinal_Empty_2 in H0. lia. destruct H4 as [y H4]. specialize (H y H4). contradiction. contradiction.
    - intros A H1 k. pose proof (Empty_or_exists_In U A) as [H2 | [x H2]].
      -- apply cardinal_Empty_1 in H2. assert (S m = 0) as H3. { apply cardinal_unicity with (X := A); auto. } lia.
      -- assert (k = 0 \/ k > 0) as [H3 | H3] by lia; subst.
         * rewrite n_choose_0. replace (Subsets_of_Cardinality A 0) with (⦃⦃⦄⦄ : Ensemble (Ensemble U)). apply cardinal_Singleton.
           apply set_equal_def. intros y. split; intro H4. apply In_singleton_def in H4. rewrite H4. unfold Subsets_of_Cardinality. split.
           apply Empty_Subset. apply card_empty. unfold Subsets_of_Cardinality in H4. destruct H4 as [H4 H5]. apply cardinal_Empty_1 in H5. autoset.
         * rewrite Union_of_Subsets with (x := x); auto. replace (S m) with (m + 1) by lia. rewrite binomial_recursion_2; try lia. apply cardinal_Union.
           + specialize (IH (A − ⦃x⦄)). replace (Subsets_without_x A x k) with (Subsets_of_Cardinality (A − ⦃x⦄) k).
             2 : { unfold Subsets_of_Cardinality, Subsets_without_x. apply set_equal_def. intros y; split; intros H4.
                   - unfold In in H4. destruct H4 as [H4 H5]. split; auto. rewrite Subset_def in H4.
                     rewrite Subset_def. intros z H6. specialize (H4 z H6). autoset. split; autoset. intros H6. rewrite Subset_def in H4.
                     specialize (H4 x H6). apply In_Setminus_def in H4 as [_ H4]. apply H4. autoset.
                   - unfold In. destruct H4 as [H4 [H5 H6]]. split; auto. rewrite Subset_def in H4. rewrite Subset_def. intros z H7.
                     specialize (H4 z H7). apply In_Setminus_def. split. autoset. intros H8. apply In_singleton_def in H8. subst. contradiction.
             }
             apply IH. apply cardinal_minus; auto.
           + replace (Subsets_with_x A x k) with (Im (Ensemble U) (Ensemble U) (Subsets_of_Cardinality (A − ⦃x⦄) (k - 1)) (fun S : Ensemble U => Add U S x)).
             2 : { apply set_equal_def. intros y. split; intros H4.
                   - apply In_Im_def in H4 as [S [H4 H5]]. unfold Subsets_with_x. unfold Subsets_of_Cardinality in H4. destruct H4 as [H4 H6].
                     split; auto. unfold Add in H5. rewrite Subset_def. intros z H7. rewrite <- H5 in H7. apply In_Union_def in H7 as [H7 | H7].
                     rewrite Subset_def in H4. specialize (H4 z H7). autoset. apply In_singleton_def in H7. autoset. split.
                     unfold Add in H5. autoset. rewrite <- H5. replace k with (Datatypes.S (k - 1)) by lia. apply card_add; auto. intros H7.
                     rewrite Subset_def in H4. specialize (H4 x H7). apply In_Setminus_def in H4 as [_ H4]. apply H4. autoset.
                   - unfold Subsets_with_x in H4. destruct H4 as [H4 [H5 H6]]. apply In_Im_def. exists (y − ⦃x⦄). split.
                     -- unfold Subsets_of_Cardinality. split; auto. rewrite Subset_def. intros z H7. rewrite Subset_def in H4. specialize (H4 z).
                        assert (z ∈ y) as H8 by autoset. specialize (H4 H8). apply In_Setminus_def. split. autoset. intros H9. apply In_singleton_def in H9.
                        rewrite H9 in H7. apply In_Setminus_def in H7 as [_ H7]. apply H7. autoset. apply cardinal_minus; autoset. replace (Datatypes.S (k - 1)) with k by lia. autoset.
                     -- unfold Add. apply set_equal_def. intros z. split; intros H7. apply In_Union_def in H7 as [H7 | H7]; autoset. apply In_singleton_def in H7. autoset.
                        apply In_Union_def. pose proof classic (z = x) as [H8 | H8]. right. autoset. left. apply In_Setminus_def. split; autoset.
                 }
              apply Add_not_in_preserves_cardinality. intros y H4. unfold Subsets_of_Cardinality in H4. destruct H4 as [H4 H5]. rewrite Subset_def in H4. intros H6. specialize (H4 x).
              specialize (H4 H6). apply In_Setminus_def in H4 as [_ H4]. apply H4. autoset. apply IH. apply cardinal_minus; autoset.
           + unfold Subsets_without_x, Subsets_with_x. apply set_equal_def. intros y. split; intros H4.
             ** apply In_Intersection_def in H4 as [H4 H5]. unfold In in H4, H5. autoset.
             ** apply In_Intersection_def. unfold In. autoset.
Qed.

End num_subsets.

Lemma list_to_ensemble_card_nodup : forall (U : Type) (l : list U),
  NoDup l -> ‖list_to_ensemble l‖ = length l.
Proof.
  intros U l H1. induction l as [| h t IH].
  - rewrite list_to_ensemble_nil. apply card_empty.
  - rewrite list_to_ensemble_cons. replace (length (h :: t)) with (1 + length t). 2 : { simpl. lia. }
    apply cardinal_Union. apply cardinal_Singleton. apply IH. apply NoDup_cons_iff in H1 as [H1 H2]. auto.
    apply set_equal_def. intros x. split; intros H2; autoset. apply In_Intersection_def in H2 as [H2 H3].
    apply In_singleton_def in H2. apply In_list_to_ensemble in H3. subst. apply NoDup_cons_iff in H1 as [H1 H4]; tauto.
Qed.

Lemma empty_domain_not_bijective : forall (U V : Type) (E : Ensemble V) (f : (subType (∅ : Ensemble U)) -> subType E),
  E ≠ ∅ -> ~ bijective f.
Proof.
  intros U V E f H1 [_ H2]. unfold surjective in H1.
  pose proof (not_Empty_In V E) as [H3 _]. specialize (H3 H1) as [x H3].
  set (y := mkSubType V E x H3). specialize (H2 y) as [[val prop] H2]. autoset.
Qed.

Lemma empty_domain_neq : forall (U V : Type) (f : U -> (subType (∅ : Ensemble V))),
  forall x y : U, f x ≠ f y.
Proof.
  intros U V f x y H1. destruct (f x) as [val prop]. autoset.
Qed.

Lemma empty_range_bijective : forall (U V : Type) (E : Ensemble U) (f : (subType E) -> subType (∅ : Ensemble V)),
  bijective f.
Proof.
  intros U V E f. split.
  - unfold injective. intros x y H2. exfalso. pose proof (empty_domain_neq (subType E) V f x y) as H3. auto.
  - intros [val prop]. pose proof not_In_Empty V val as H2. autoset.
Qed.

Lemma empty_function_bijective : forall (U V : Type) (f : (subType (∅ : Ensemble U)) -> subType (∅ : Ensemble V)),
  bijective f.
Proof.
  intros U V f. split.
  - unfold injective. intros x y H1. exfalso. pose proof (empty_domain_neq (subType (∅ : Ensemble U)) V f x y) as H2. auto.
  - intros [val prop]. pose proof not_In_Empty V val as H1. autoset.
Qed.

Lemma cardinal_finite_eq_list_with_length : forall (U : Type) (A : Ensemble U) (n : nat),
  ‖A‖ = n -> exists l : list U, A = list_to_ensemble l /\ length l = n /\ NoDup l.
Proof.
  intros U A n H1. pose proof H1 as H2. apply cardinal_finite in H1. apply Finite_set_equiv_Finite in H1.
  apply Finite_set_iff_Finite_set' in H1 as [l' [H1 H3]]. exists l'. split; auto. split; auto.
  apply list_to_ensemble_card_nodup in H1. subst. apply cardinal_unicity with (U := U) (X := (list_to_ensemble l')); auto.
Qed.

Theorem Pigeonhole : forall (U V : Type) (A : Ensemble U) (B : Ensemble V)
  (f : subType A -> subType B) (n m : nat),
    ‖B‖ = n -> ‖A‖ = m -> 0 < n < m -> ~ injective f.
Proof.
  intros U V A B f n m H1 H2 [H3 H4] H5. apply cardinal_finite_eq_list_with_length in H1 as [l [H1 [H6 H7]]].
  apply cardinal_finite_eq_list_with_length in H2 as [l' [H2 [H8 H9]]]. subst. unfold injective in H5.
  assert (forall x : (subType (list_to_ensemble l')), List.In (val (list_to_ensemble l') x) l') as H10.
  { intros x. destruct x as [val prop]. simpl. apply In_list_to_ensemble. auto. }
  assert (forall x : (subType (list_to_ensemble l)), List.In (val (list_to_ensemble l) x) l) as H11.
  { intros x. destruct x as [val prop]. simpl. apply In_list_to_ensemble. auto. }
  assert (forall x : subType (list_to_ensemble l'), List.In (val (list_to_ensemble l) (f x)) l) as H12.
  { intros x. specialize (H11 (f x)). auto. }
Admitted.

Lemma cardinal_eq_Finite : forall (U V : Type) (A : Ensemble U) (B : Ensemble V),
  Finite_set A -> Finite_set B -> ‖A‖ = ‖B‖ -> exists m n : nat, ‖A‖ = m /\ ‖B‖ = n /\ m = n.
Proof.
  intros U V A B. repeat rewrite Finite_set_iff_Finite_set'. intros [l1 [H1 H2]] [l2 [H3 H4]] [[H5 H6] | [H5 [H6 [f H7]]]].
  - exists 0, 0. repeat split; auto. rewrite H5. apply card_empty. rewrite H6. apply card_empty.
  - exists (length l1), (length l2). repeat split; try (subst; apply list_to_ensemble_card_nodup; auto).
    assert (length l1 = length l2 \/ length l2 < length l1 \/ length l2 > length l1) as [H8 | [H8 | H8]] by lia; auto.
    -- assert (length l2 = 0 \/ length l2 > 0) as [H9 | H9] by lia.
       + apply length_zero_iff_nil in H9. subst. simpl in H6. autoset. 
       + exfalso. apply (Pigeonhole U V A B f (length l2) (length l1)); subst. apply list_to_ensemble_card_nodup; auto.
         apply list_to_ensemble_card_nodup; auto. lia. destruct H7 as [H7 _]. apply H7.
    -- admit.
Admitted.