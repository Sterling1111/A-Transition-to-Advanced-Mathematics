Require Import Imports.

Notation ℕ := nat.
Notation ℤ := Z.
Notation ℚ := Q.
Notation ℝ := R.

Notation "A ⇒ B" := (A -> B) (at level 99, right associativity) : type_scope.
Notation "A ⟺ B" := (A <-> B) (at level 99, no associativity) : type_scope.

(* Notation "'∀' x , P" := (forall x, P)
  (at level 200, x ident, P at level 200, only parsing).

Notation "'∃' x , P" := (exists x, P)
  (at level 200, x ident, P at level 200).

Notation "∀ x : T , P" := (forall x : T, P)
  (at level 200, x ident, T at level 200, P at level 200, only parsing).

Notation "∃ x , P" := (exists x, P)
  (at level 200, x ident, P at level 200, only parsing).

Notation "∃ x : T , P" := (exists x : T, P)
  (at level 200, x ident, T at level 200, P at level 200, only parsing). *)

Notation "| x |" := (Rabs x) 
  (at level 200, x at level 0, format "| x |", no associativity) : R_scope.

Notation "√ x" := (sqrt x) (format "√ x", at level 20).

Open Scope R_scope.

Declare Scope interval_scope.
Delimit Scope interval_scope with interval.

Module IntervalNotations.
  Notation "[ a , b ]" := (fun x => a <= x <= b) (only parsing) : interval_scope.
  Notation "[ a , b ⦆" := (fun x => a <= x < b) (only parsing) : interval_scope.
  Notation "⦅ a , b ]" := (fun x => a < x <= b) (only parsing) : interval_scope.
  Notation "⦅ a , b ⦆" := (fun x => a < x < b) (only parsing) : interval_scope.

  Notation "⦅-∞ , b ⦆" := (fun x => x < b) (only parsing) : interval_scope.
  Notation "⦅ -∞ , b ]" := (fun x => x <= b) (only parsing) : interval_scope.
  Notation "⦅ a , +∞]" := (fun x => a < x) (only parsing) : interval_scope.
  Notation "[ a , +∞⦆" := (fun x => a <= x) (only parsing) : interval_scope.

  Notation "⦅-∞ , +∞⦆" := (Full_set _) (only parsing) : interval_scope.
End IntervalNotations.