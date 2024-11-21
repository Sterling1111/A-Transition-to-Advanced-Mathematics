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
  (limit f (Full_set ℝ) a L) 
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

Lemma limit_of_function_unique : forall D f a L1 L2,
  ⟦ lim a ⟧ f D = L1 -> ⟦ lim a ⟧ f D = L2 -> L1 = L2.
Proof.
  intros D f a L1 L2 [[b [c [H1 H2]]] H3] [_ H4]. pose proof (classic (L1 = L2)) as [H5 | H5]; auto.
  assert (c > a) as H0. { nra. } specialize (H3 (|L1 - L2| / 2) ltac:(solve_abs)) as [δ1 [H6 H7]].
  specialize (H4 (|L1 - L2| / 2) ltac:(solve_abs)) as [δ2 [H8 H9]].
  set (δ := Rmin δ1 δ2). assert (δ > 0) as H10 by (unfold δ; solve_min).
  set (y := Rmin (a + δ / 2) c). assert (y ∈ D) as H11. { apply H2. unfold In. unfold y; solve_min. }
  set (x := mkRsub D y H11). assert (H12 : y <= a + δ1 / 2). { unfold y. unfold δ. solve_min. }
  assert (0 < |x - a| < δ1) by admit. assert (0 < |x - a| < δ2) by admit. specialize (H7 x ltac:(auto)).
  specialize (H9 x ltac:(auto)). solve_abs.
Admitted.