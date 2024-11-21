Require Import Imports Sequence Sets Chapter12 Reals_util Sequence.
Import SetNotations.

Open Scope R_scope.

Notation "'∀' x , P" := (forall x, P)
  (at level 200, x ident, P at level 200, only parsing).

Notation "'∃' x , P" := (exists x, P)
  (at level 200, x ident, P at level 200).

Notation "∀ x : T , P" := (forall x : T, P)
  (at level 200, x ident, T at level 200, P at level 200, only parsing).

Notation "∃ x , P" := (exists x, P)
  (at level 200, x ident, P at level 200, only parsing).

Notation "∃ x : T , P" := (exists x : T, P)
  (at level 200, x ident, T at level 200, P at level 200, only parsing).

Definition encloses (D : Ensemble R) (a : R) : Prop :=
  exists b c, b < a < c /\ (fun x => b <= x <= c) ⊆ D.

Record Rsub (D : Ensemble R) := mkRsub {
  x :> R;
  cond : x ∈ D
}.

Definition limit (D : Ensemble R) (f : Rsub D -> R) (a : Rsub D) (L : R) : Prop :=
  encloses D a /\
    (∀ ε, ε > 0 ⇒ ∃ δ, δ > 0 /\ ∀ x : Rsub D, 0 < |x - a| < δ ⇒ |f x - L| < ε).

Notation "⟦ 'lim' a ⟧ f '=' L" := 
  (limit (Full_set ℝ) f a L) 
    (at level 70, f at level 0, no associativity, format "⟦  'lim'  a  ⟧  f  '='  L").

Notation "⟦ 'lim' a ⟧ f D '=' L" := 
  (limit D f a L) 
    (at level 70, f at level 0, D at level 0, no associativity, format "⟦  'lim'  a  ⟧  f  D  '='  L").

(*
Definition limit_pos_inf (f : ℝ -> ℝ) (L : ℝ) : Prop :=
  ∀ ε, ε > 0 ⇒
    ∃ N, ∀ x, x > N ⇒ |f x - L| < ε.

Definition limit_neg_inf (f : ℝ -> ℝ) (L : ℝ) : Prop :=
  ∀ ε, ε > 0 ⇒
    ∃ N, ∀ x, x < N ⇒ |f x - L| < ε.

Definition limit_right (f : ℝ -> ℝ) (D : Ensemble ℝ) (a L : ℝ) : Prop :=
  ∀ ε, ε > 0 ⇒
    ∃ δ, ∀ x, x ∈ D ⇒ 0 < x - a < δ ⇒ |f x - L| < ε.

Definition limit_left (f : ℝ -> ℝ) (D : Ensemble ℝ) (a L : ℝ) : Prop :=
  ∀ ε, ε > 0 ⇒
    ∃ δ, ∀ x, x ∈ D ⇒ 0 < a - x < δ ⇒ |f x - L| < ε.

Notation "⟦ 'lim' a ⟧ f D '=' L" := 
  (limit f D a L) 
  (at level 70, f at level 0, D at level 0, no associativity, format "⟦  'lim'  a  ⟧  f  D  '='  L").

Notation "⟦ 'lim' ∞ ⟧ f '=' L" := 
  (limit_pos_inf f L)
  (at level 70, f at level 0, no associativity, format "⟦  'lim' ∞  ⟧  f  '='  L").

Notation "⟦ 'lim' -∞ ⟧ f '=' L" := 
  (limit_neg_inf f L)
  (at level 70, f at level 0, no associativity, format "⟦  'lim'  -∞  ⟧  f  '='  L").

Notation "⟦ 'lim' a ⁺ ⟧ f '=' L" := 
  (limit_right f (Full_set ℝ) a L)
  (at level 70, f at level 0, no associativity, format "⟦  'lim'  a ⁺  ⟧  f  '='  L").

Notation "⟦ 'lim' a ⁻ ⟧ f '=' L" := 
  (limit_left f (Full_set ℝ) a L)
  (at level 70, f at level 0, no associativity, format "⟦  'lim'  a ⁻  ⟧  f  '='  L").

*)

Lemma limit_of_function_unique' : forall D f a L1 L2,
  ⟦ lim a ⟧ f D = L1 -> ⟦ lim a ⟧ f D = L2 -> L1 = L2.
Proof.
  intros D f a L1 L2 [[b [c [H1 H2]]] H3] [_ H4]. pose proof (classic (L1 = L2)) as [H5 | H5]; auto.
  specialize (H3 (|L1 - L2| / 2) ltac:(solve_abs)) as [δ1 [H6 H7]].
  specialize (H4 (|L1 - L2| / 2) ltac:(solve_abs)) as [δ2 [H8 H9]].
  set (δ := Rmin δ1 δ2). set (y := Rmin (a + δ / 2) c).
  assert (δ > 0) as H10 by (unfold δ; solve_min).
  assert (y ∈ D) as H11. { apply H2. unfold In. unfold y. solve_min. }
  set (x := mkRsub D y H11). assert (δ <= δ1 /\ δ <= δ2) as [H12 H13] by (unfold δ; solve_min).
  assert (y <= c /\ y <= a + δ / 2) as [H14 H15] by (unfold y; solve_min).
  assert (y > a) as H16 by (unfold y; solve_min). assert (0 < |y - a| < δ) as H19 by solve_abs.
  assert (0 < |x - a| < δ1 /\ 0 < |x - a| < δ2) as [H20 H21] by (unfold x, δ; simpl; solve_abs).
  specialize (H9 x ltac:(auto)). specialize (H7 x ltac:(auto)).
  (* instead of all this we could just do solve_abs *)
  assert (|L1 - L2| < |L1 - L2|).
  {
    assert (|(L1 - f x + (f x - L2))| <= |L1 - f x| + |f x - L2|) as H22 by (apply Rabs_triang).
    rewrite Rabs_minus_sym in H22. 
    assert (|f x - L1| + |f x - L2| < |L1 - L2| / 2 + |L1 - L2| / 2) as H23 by lra.
    field_simplify in H23. rewrite Rmult_div_r in H23; auto.
    replace (L1 - f x + (f x - L2)) with (L1 - L2) in H22 by lra. lra.
  } lra.
Qed.

Lemma limit_of_function_unique : forall f a L1 L2,
  ⟦ lim a ⟧ f = L1 -> ⟦ lim a ⟧ f = L2 -> L1 = L2.
Proof.
  intros f a L1 L2 H1 H2. apply (limit_of_function_unique' (Full_set ℝ) f a L1 L2); auto.
Qed.

