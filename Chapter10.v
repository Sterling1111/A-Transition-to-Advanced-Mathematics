Require Import Imports Sets.
Require Export Chapter9.

Import SetNotations.

Open Scope R_scope.

Lemma lemma_10_1_a : 3 ∈ ⦃ 1, 2, 3, 4, 5, 6, 7 ⦄.
Proof. autoset. Qed.

Axiom PI_int_bound : 3 < PI < 4.

Lemma lemma_10_1_b : PI ∉ ⦃ 1, 2, 3, 4, 5, 6, 7 ⦄.
Proof.
  pose proof PI_int_bound as H1. autoset.
Qed.

Lemma lemma_10_1_c : PI ∈ Full_set R.
Proof.
  apply Full_intro.
Qed.

Lemma frac_not_Z : forall (x : Z) (a b : R), (exists z1, IZR z1 < a / b < IZR (z1 + 1)) -> a / b <> IZR x.
Proof.
  intros x a b [z1 H1] H2. pose proof (classic (a = 0)) as [H3 | H3]; pose proof (classic (b = 0)) as [H4 | H4];
   try (replace (a / b) with 0 in H1 by (subst; unfold Rdiv; try rewrite Rinv_0; lra); assert (z1 < 0 < z1 + 1)%Z as H5 by (split; first [apply lt_IZR | apply IZR_lt]; lra); lia).
   rewrite H2 in H1. destruct H1 as [H1 H5]. apply lt_IZR in H1. apply lt_IZR in H5. lia.
Qed.

Section section_10_1_d_e.
  Let A : Ensemble R := fun x => x < 1.
  Let B : Ensemble R := fun x => x < 1 /\ exists y, x = IZR y.

  Lemma lemma_10_1_d : 2/3 ∈ A.
  Proof.
    unfold In, A. lra.
  Qed.

  Lemma lemma_10_1_e : 2/3 ∉ B.
  Proof.
    unfold In, B. intros [H1 H2]. destruct H2 as [y H2]. 
    assert (2 / 3 <> IZR y) as H3. { apply frac_not_Z. exists 0%Z. simpl. lra. } auto.
  Qed.
  
End section_10_1_d_e.


Close Scope R_scope.

Section section_10_2.
  Let A : Ensemble (Z * Z) := fun  p =>
    let (x, y) := p in (4 | x - y).

  Let B : Ensemble (Z * Z) := fun p =>
    let (x, y) := p in (Z.Even x <-> Z.Even y).

  Lemma lemma_10_2 : A ⊆ B.
  Proof.
    unfold Included. intros (x, y) [i H1]. unfold In, A, B in *. split.
    - intros H2. destruct (Z.Even_or_Odd y) as [H3 | H3]; auto.
      assert (H4 : Z.Even (x - y)). { exists (2*i). lia. }
      assert (H5 : Z.Odd (x - y)). { apply odd_plus_Z. left; split; (try  rewrite <- odd_sign_Z); auto. }
      exfalso. apply Z.Even_Odd_False with (x := x - y); auto.
    - intros H2. assert (Z.Even (x - y)) as H3. { exists (2*i); lia. }
      apply even_plus_Z in H3 as [[H3 _] | [_ H3]]; auto. rewrite <- odd_sign_Z in H3. exfalso.
      apply Z.Even_Odd_False with (x := y); auto.
  Qed.
End section_10_2.

Section section_10_3.
  Let X : Ensemble Z := fun x => x ≡ -1 (mod 6).

  Let Y : Ensemble Z := fun y => y ≡ 2 (mod 3).

  Lemma lemma_10_3 : X ⊆ Y.
  Proof.
    unfold Included. intros x H1. unfold In, X, Y in *.
    destruct H1 as [k H2]. unfold Zmod_equiv. unfold Z.divide. exists (2 * k - 1). lia.
  Qed.
  
End section_10_3.

Lemma lemma_10_4_a : forall (U : Type) (A B : Ensemble U),
  (A ⋂ B)′ ⊆ (A′ ⋃ B′).
Proof.
  intros U A B x H1. solve_in_Intersection_Union_helper_2.
Qed.

Lemma lemma_10_4_b : forall (U : Type) (A B : Ensemble U),
  (A′ ⋃ B′) ⊆ (A ⋂ B)′.
Proof.
  intros U A B x. solve_in_Intersection_Union_helper_2.  
Qed.

Lemma lemma_10_4_c : forall (U : Type) (A B : Ensemble U),
  (A ⋂ B)′ = (A′ ⋃ B′).
Proof.
  solve_set_equality_auto.
Qed.

Lemma lemma_10_5 : forall (U : Type) (X Y : Ensemble U),
  (X − (X − Y)) ⊆ X ⋂ Y.
Proof.
  intros U X Y x H1. solve_in_Intersection_Union_helper_2.
Qed.

Lemma lemma_10_6 : forall (U : Type) (X : Ensemble U),
  X ⋃ ∅ = X.
Proof. autoset. Qed.

Section section_10_7.
  Variable n : Z.
  Let A : Ensemble Z := fun x => (n | x).
  Let B : Ensemble Z := fun x => x ≡ 0 (mod n).

  Lemma lemma_10_7 : A = B.
  Proof.
    apply set_equal_def. intros x. split.
    - intros H1. unfold In, A, B in *. destruct H1 as [k H1]. exists k. lia.
    - intros H1. unfold In, A, B in *. destruct H1 as [k H1]. exists k. lia.
  Qed.
End section_10_7.

Lemma lemma_10_8_a : forall (U : Type) (A B C : Ensemble U),
  A − (B ⋂ C) ⊆ (A − B) ⋃ (A − C).
Proof.
  intros U A B C x H1. solve_in_Intersection_Union_helper_2.
Qed.

Lemma lemma_10_8_b : forall (U : Type) (A B C : Ensemble U),
  (A − B) ⋃ (A − C) ⊆ A − (B ⋂ C).
Proof.
  intros U A B C x H1. solve_in_Intersection_Union_helper_2.
Qed.

Lemma lemma_10_8_c : forall (U : Type) (A B C : Ensemble U),
  A − (B ⋂ C) = (A − B) ⋃ (A − C).
Proof.
  autoset.
Qed.

Section section_10_9.
  Let Sn (n : nat) : Ensemble Z :=
    fun m : Z => m <= Z.of_nat n.

  Let Union_Sn_a (i : nat) : Ensemble Z :=
    Union_f_n Sn i.

  Lemma lemma_10_9_a : forall n : nat,
    Union_Sn_a n = Sn n.
  Proof.
    intros n. induction n as [| k IH]; try reflexivity.
    unfold Union_Sn_a in *. rewrite Union_f_n_S. rewrite IH. apply set_equal_def. intros x. split; intros H1.
    - apply In_Union_def in H1 as [H1 | H1].
      -- unfold In, Sn in *. lia.
      -- apply H1.
    - apply In_Union_def. right. apply H1.
  Qed.

  Let Union_Sn_b : Ensemble Z :=
    fun x : Z => exists n : nat, x ∈ Sn n.

  Lemma lemma_10_9_b : Union_Sn_b = Full_set Z.
  Proof.
    apply set_equal_def. intros x. split.
    - intros H1. apply Full_intro.
    - intros H1. repeat unfold In, Union_Sn_b, Sn.
      exists (Z.to_nat x). lia.
Qed.

End section_10_9.