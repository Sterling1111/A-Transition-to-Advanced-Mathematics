Require Import Reals Lra Lia Reals_util Arith Nat PeanoNat Sequence List.
Import ListNotations.
Require Export Chapter20.

Open Scope R_scope.

Ltac compare_elems e1 e2 := 
  let e1' := eval simpl in e1 in
  let e2' := eval simpl in e2 in
  first [
    field_simplify; try nra |
    field_simplify; try nia |  
    congruence
  ].

(* Compare two lists recursively element by element *)
Ltac compare_lists_step :=
  match goal with
  | [ |- [] = [] ] => reflexivity
  | [ |- (?x :: ?xs) = (?y :: ?ys) ] => 
      first [
        assert (x = y) by compare_elems x y;
        apply f_equal2; [assumption | compare_lists_step]
        |
        fail "Elements" x "and" y "cannot be proven equal"
      ]
  | [ |- ?l1 = ?l2 ] =>
      fail "Lists" l1 "and" l2 "have different lengths or structures"
  end.

Ltac prove_lists_equal :=
  intros; compute;
  try solve [reflexivity];
  compare_lists_step.

Section section_34_1.
  Definition a : sequence := fun n => 5 - 3 * INR n.
  Definition b : sequence := fun n => 4 * 2 ^ n.
  Definition c : sequence := fun n => 1 / 2 + 3 * INR n / 4.
  Definition d : sequence := fun n => (3 / 5) * (2 / 3) ^ n.

  Lemma lemma_34_1_a : map a (seq 0 6) = [5; 2; -1; -4; -7; -10].
  Proof. prove_lists_equal. Qed.

  Lemma lemma_34_1_b : map b (seq 0 6) = [4; 8; 16; 32; 64; 128].
  Proof. prove_lists_equal. Qed.

  Lemma lemma_34_1_c : map c (seq 0 6) = [2/4; 5/4; 8/4; 11/4; 14/4; 17/4].
  Proof. prove_lists_equal. Qed.

  Lemma lemma_34_1_d : map d (seq 0 6) = [3/5; 2/5; 4/15; 8/45; 16/135; 32/405].
  Proof. prove_lists_equal. Qed.

End section_34_1.

Section section_34_2.
  Definition prop_34_2_a := limit_of_sequence (fun n => 3 - 4 / INR n) 3.

  Lemma prop_34_2_a_symbolic : prop_34_2_a = forall ε : ℝ, ε > 0 ⇒ (exists N : ℝ, forall n : ℕ, INR n > N ⇒ Rabs (3 - 4 / INR n - 3) < ε).
  Proof.
    unfold prop_34_2_a, limit_of_sequence. reflexivity.
  Qed.
        
  Definition prop_34_2_b := ~limit_of_sequence (fun n => 6) 3.
  
  Lemma prop_34_2_b_symbolic : prop_34_2_b = exists ε : ℝ, ε > 0 ⇒ forall N : ℝ, exists n : ℕ, INR n > N ⇒ Rabs (6 - 3) >= ε.
  Proof.
    unfold prop_34_2_b, limit_of_sequence. apply 

End section_34_2.