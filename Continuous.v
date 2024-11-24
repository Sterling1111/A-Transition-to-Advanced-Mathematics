Require Import Imports Limit Sums Chapter36.

Definition continuous_at_a (D : Ensemble R) (f : Rsub D -> R) (a : Rsub D) : Prop :=
  ⟦ lim a ⟧ f D = f a.

Definition continuous_on (D : Ensemble R) (f : Rsub D -> R) : Prop :=
  ∀ a : Rsub D, continuous_at_a D f a.

Example example_37_2 : forall c d,
  continuous_on (Full_set R) (fun x => c * x + d).
Proof.
  intros c d a. apply lemma_36_2.
Qed.

Definition polynomial (l : list R) : R -> R :=
  fun x => sum_f 0 (length l - 1) (fun i => nth i l 0 * x^(length l - 1 - i)).

Lemma poly_nil : forall x, polynomial [] x = 0.
Proof.
  intro; compute; lra.
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

Example example_37_3 : forall x, polynomial [3; 3; 1] x = 3 * x^2 + 3 * x + 1.
Proof. intro x. compute; field_simplify. reflexivity. Qed.

Theorem theorem_37_14 : forall l a,
  continuous_at_a (Full_set R) (polynomial l) a.
Proof.
  intros l a. induction l as [| h t IH].
  - replace ((fun x : Rsub (Full_set R) => polynomial [] x)) with (fun x : Rsub (Full_set R) => 0).
    2 : { extensionality x. rewrite poly_nil. reflexivity. } unfold continuous_at_a. solve_lim.
  - replace ((fun x : Rsub (Full_set R) => polynomial (h :: t) x)) with (fun x : Rsub (Full_set R) => h * x^(length t) + polynomial t x).
    2 : { extensionality x. rewrite poly_cons. reflexivity. } 
    unfold continuous_at_a. solve_lim.
Qed.

Theorem theorem_37_14' : forall l,
  continuous_on (Full_set R) (polynomial l).
Proof.
  intros l a. apply theorem_37_14.
Qed.

Lemma poly_c_example : continuous_on (Full_set R) (fun x => 5*x^5 + 4*x^4 + 3*x^3 + 2*x^2 + x + 1).
Proof.
  unfold continuous_on. intros a. unfold continuous_at_a. solve_lim.
Qed.