Require Import Imports Sequence Sets Chapter12.
Import SetNotations.

Open Scope R_scope.

Definition limit (f : ℝ -> ℝ) (D : Ensemble R) (a L : ℝ) : Prop := 
  forall ε : ℝ, ε > 0 ⇒
    exists δ : ℝ, forall x : ℝ, x ∈ D ⇒ 0 < |x - a| < δ ⇒ |f x - L| < ε.

Definition continuous (f : ℝ -> ℝ) (D : Ensemble ℝ) : Prop :=
  forall a : ℝ, a ∈ D ⇒ limit f D a (f a).

Lemma pow_2_continuous : continuous (fun x => x ^ 2) (Full_set ℝ).
Proof.
  unfold continuous, limit. intros a Ha ε Hε.
  exists (sqrt ε). intros x Hx Hx'.
  assert (Hx'' : 0 < |x - a| < sqrt ε) by lra.
  assert (Hx''' : |x - a| ^ 2 < ε) by (apply sqrt_lt_1_alt; lra).
  assert (Hx'''' : |x ^ 2 - a ^ 2| < ε) by (rewrite <- Rabs_Ropp; apply Rabs_def1; lra).
  rewrite Rabs_minus_sym. apply Hx''''.
Qed.