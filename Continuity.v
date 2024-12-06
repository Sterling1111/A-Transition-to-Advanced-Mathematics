Require Import Imports Limit Sums Reals_util Sets Notations Functions.
Import SetNotations.

Definition continuous_at (D : Ensemble R) (f : Rsub D -> R) (a : Rsub D) : Prop :=
  ⟦ lim a ⟧ f D = f a.

Definition continuous_on (D : Ensemble R) (f : Rsub D -> R) : Prop :=
  ∀ a : Rsub D, continuous_at D f a.

Example example_37_2 : forall c d,
  continuous_on R (fun x => c * x + d).
Proof.
  intros c d a. unfold continuous_at. unfold Type_to_Ensemble in *. solve_lim.
Qed.

Section section_37_3.
  Let f (x : R) : R :=
    match Rle_dec 0 x, Rle_dec x 1 with
    | left _, left _ => 1
    | _, _ => 0
    end.

  Lemma f_spec : forall x,
    (0 <= x <= 1)%R -> f x = 1 /\ (x < 0 \/ x > 1)%R -> f x = 0.
  Proof.
    intros x H1 [H2 H3]. unfold f. destruct (Rle_dec 0 x), (Rle_dec x 1); simpl in *; lra.
  Qed.

  Let a := mkRsub R 1 ltac:(apply Full_intro).

  Example example_37_3 : ~ continuous_at R f a.
  Proof.
    intros [H1 H2]. unfold Type_to_Ensemble in *. simpl in H2. specialize (H2 (1/2) ltac:(lra)) as [δ [H3 H4]].
    set (x := mkRsub (Full_set R) (1 + δ/2) ltac:(apply Full_intro)).
    specialize (H4 x ltac:(simpl; solve_abs)). replace (f x) with 0 in H4.
    2 : { unfold f. destruct (Rle_dec 0 x), (Rle_dec x 1); simpl in *; lra. }
    replace (f 1) with 1 in H4. 2 : { unfold f. destruct (Rle_dec 0 1), (Rle_dec 1 1); simpl in *; lra. }
    solve_abs.
  Qed.
End section_37_3.

Section section_37_4.
  Let f : Rsub (fun x => 0 <= x) -> R := fun x => x.
  Let D : Ensemble R := fun x => 0 <= x.
  
  Lemma H1 : 0 ∈ D.
  Proof.
    unfold D. unfold In. lra.
  Qed.

  Let a := mkRsub (fun x => 0 <= x) 0 H1.

  Example example_37_4 : ~ continuous_at D f a.
  Proof.
    intros [[b [c [H1 H2]]] _]. simpl in H1. specialize (H2 (b / 2) ltac:(unfold In; lra)).
    unfold In, D in H2. lra.
  Qed.

End section_37_4.

Lemma lemma_37_11_a : forall D f g a,
  continuous_at D f a -> continuous_at D g a -> continuous_at D (f + g)%f a.
Proof.
  intros D f g a H1 H2. unfold continuous_at in *. pose proof H1 as [H3 _]. apply limit_plus; auto.
Qed.

Lemma lemma_37_11_b : forall D f g a,
  continuous_at D f a -> continuous_at D g a -> continuous_at D (f ∙ g)%f a.
Proof.
  intros D f g a H1 H2. unfold continuous_at in *. pose proof H1 as [H3 _]. apply limit_mult; auto.
Qed.

Lemma lemma_37_11_c : forall D f g a,
  g a ≠ 0 -> continuous_at D f a -> continuous_at D g a -> continuous_at D (f / g)%f a.
Proof.
  intros D f g a H1 H2 H3. unfold continuous_at in *. pose proof H2 as [H4 _]. apply limit_div; auto.
Qed.

Definition polynomial' (l : list R) : (Rsub (Full_set R)) -> R :=
  fun x => sum_f 0 (length l - 1) (fun i => nth i l 0 * x^(length l - 1 - i)).

Definition polynomial (l : list R) : R -> R :=
  fun x => sum_f 0 (length l - 1) (fun i => nth i l 0 * x^(length l - 1 - i)).

Lemma poly_equiv : forall l, polynomial' l = polynomial l.
Proof.
  intros l. apply functional_extensionality. intros x. unfold polynomial, polynomial'.
  apply sum_f_equiv; try lia. intros k H1. reflexivity.
Qed.

Lemma poly_nil : forall x, polynomial [] x = 0.
Proof.
  intro; compute. rewrite Rmult_1_r. reflexivity.
Qed.

Lemma poly_cons : forall h t x, polynomial (h :: t) x = h * x^(length t) + polynomial t x.
Proof.
  intros h t x. unfold polynomial. assert (length t = 0 \/ length t > 0)%nat as [H1 | H1] by lia.
  - rewrite length_zero_iff_nil in H1. subst; simpl; repeat rewrite sum_f_0_0; lra.
  - replace (length (h :: t) - 1)%nat with (length t) by (simpl; lia). rewrite sum_f_nth_cons_8; try lia.
    replace (x ^ (length t - 0) * h) with (h * x ^ (length t)). 2 : { rewrite Nat.sub_0_r; lra. }
    apply Rplus_eq_compat_l. apply sum_f_equiv; try lia. intros k H2.
    replace (length t - (k + 1))%nat with (length t - 1 - k)%nat by lia. reflexivity.
Qed.

Theorem theorem_37_14 : forall l a,
  continuous_at R (polynomial l) a.
Proof.
  intros l a. unfold Type_to_Ensemble in *. induction l as [| h t IH].
  - replace (fun x : (Rsub (Full_set R)) => polynomial [] x) with (fun x : Rsub (Full_set R) => 0).
    2 : { extensionality x. rewrite poly_nil. reflexivity. } unfold continuous_at. solve_lim.
  - replace (fun x : Rsub (Full_set R) => polynomial (h :: t) x) with (fun x : Rsub (Full_set R) => h * x^(length t) + polynomial t x).
    2 : { extensionality x. rewrite poly_cons. reflexivity. } 
    unfold continuous_at. solve_lim.
Qed.

Theorem theorem_37_14' : forall l,
  continuous_on R (polynomial l).
Proof.
  intros l a. apply theorem_37_14.
Qed.

Lemma poly_c_example : continuous_on R (fun x => 5*x^5 + 4*x^4 + 3*x^3 + 2*x^2 + x + 1).
Proof.
  replace (fun x : Rsub R => 5 * x ^ 5 + 4 * x ^ 4 + 3 * x ^ 3 + 2 * x ^ 2 + x + 1) with (polynomial' [5; 4; 3; 2; 1; 1]).
  2 : { extensionality x. compute; lra. } rewrite poly_equiv. apply theorem_37_14'.
Qed.