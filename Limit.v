Require Import Imports Sequence Sets Chapter12 Reals_util Sequence.
Import SetNotations.

Open Scope R_scope.

Notation "∀ x , P" := (forall x, P)
  (at level 200, x ident, P at level 200).

Notation "∃ x , P" := (exists x, P)
  (at level 200, x ident, P at level 200).

Definition limit (f : ℝ -> ℝ) (D : Ensemble R) (a L : ℝ) : Prop :=
  ∀ ε, ε > 0 ⇒
    ∃ δ, ∀ x, x ∈ D ⇒ 0 < |x - a| < δ ⇒ |f x - L| < ε.

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

Notation "⟦ 'lim' a ⟧ f '=' L" := 
  (limit f (Full_set ℝ) a L) 
  (at level 70, f at level 0, no associativity, format "⟦  'lim'  a  ⟧  f  '='  L").

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

Section testing_dogs.
  Let f : R -> R := (fun x => x).

  Lemma limit_of_linear_function : ⟦ lim 0 ⟧ f = 0.
  Proof.
    intros ε H1. exists ε. intros x H2 H3. replace (f x - 0) with x by (unfold f; lra). solve_abs.
  Qed.

  Lemma limit_of_linear_function_right : forall a, ⟦ lim a⁺ ⟧ f = a.
  Proof.
    intros a ε H1. exists ε. intros x H2 H3. replace (f x - a) with (x - a) by (unfold f; lra). solve_abs.
  Qed.
End testing_dogs.

Lemma limit_of_linear_function' : ⟦ lim 0 ⟧  (fun x => x) = 0.
Proof.
  intros ε H1. exists ε. intros x H2 H3. replace (x - 0) with x by lra. solve_abs.
Qed.

Definition continuous (f : ℝ -> ℝ) (D : Ensemble ℝ) : Prop :=
  ∀ a, a ∈ D ⇒ ⟦ lim a ⟧ f = f a.