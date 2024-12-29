Require Import Imports.

Notation ℕ := nat.
Notation ℤ := Z.
Notation ℚ := Q.
Notation ℝ := R.

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