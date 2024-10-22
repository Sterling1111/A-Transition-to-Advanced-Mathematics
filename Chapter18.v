Require Import ZArith Lia Classical Reals Lra Classical_sets List String
               Ensembles QArith ClassicalFacts Finite_sets Powerset Finite_sets_facts Image 
               NArith DecimalString DecimalNat DecimalNat Decimal
               Fibonacci Sums Sets Binomial QRT WI_SI_WO.

Require Export Chapter17.

Import ListNotations SetNotations Choose_Notations.

Definition linear_combination (a b n : Z) : Prop :=
  exists x y : Z, n = a * x + b * y.

Theorem theorem_18_5 : forall a b n,
  (a <> 0 \/ b <> 0) -> n > 0 -> linear_combination a b n -> (Z.gcd a b <= n)%Z /\ linear_combination a b (Z.gcd a b).
Proof.
  intros a b n H1 H2 H3.
  set (S z := exists x y : Z, z = a * x + b * y /\ a * x + b * y > 0).
  assert (H4 : forall z, S z -> z >= 0).
  { intros z H4. unfold S in H4. destruct H4 as [x [y [H4 H5]]]. lia. }
  assert (H5 : exists z, S z).
  {
    pose proof (Z.lt_trichotomy a 0) as [H5 | [H5 | H5]]; pose proof (Z.lt_trichotomy b 0) as [H6 | [H6 | H6]]; subst; unfold S; try lia;
    first [exists a,1,0;split;lia | exists(-a),(-1),0;split;lia | exists b,0,1;split;lia | exists(-b),0,(-1);split;lia].
  }
  pose proof (well_ordering_Z S H4 H5) as [s [H6 H7]].
  destruct H6 as [x [y [H6 H8]]]. set (d := Z.gcd a b).
  pose proof gcd_satisfies_gcd_theory a b as H9. unfold gcd_theory in H9.
  assert ((a =? 0) && (b =? 0) = false) as H10 by lia.
  rewrite H10 in H9. clear H10. destruct H9 as [H9 [H10 H11]].
  assert (H12 : (d | (a * x + b * y))). { apply theorem_7_15; unfold d; auto. }
  assert (H13 : d <= s). { subst; apply Z.divide_pos_le; auto; lia. }
  pose proof quotient_remainder_theorem_existence a s ltac :(lia) as [q [r [H14 H15]]].
  assert (linear_combination a b r) as H16. { exists (1 - q * x), (-q*y). lia. }
  assert (r > 0 \/ r = 0) as [H17 | H17] by lia.
  - assert (S r) as H18. { destruct H16 as [x0 [y0 H16]]; exists x0, y0; split; lia. }
    specialize (H7 r ltac :(lia) H18). lia.
  - assert (s | a) as H18. { exists q. lia. }
    pose proof quotient_remainder_theorem_existence b s ltac:(lia) as [q0[r0 [H19 H20]]].
    assert (linear_combination a b r0) as H21. { exists (-q0 * x), (1 - q0 * y). nia. }
    assert (r0 > 0 \/ r0 = 0) as [H22 | H22] by lia.
    -- assert (S r0) as H23. { destruct H21 as [x0 [y0 H21]]; exists x0, y0; split; lia. }
       specialize (H7 r0 ltac:(lia) H23). lia.
    -- assert (s | b) as H23. { exists q0. lia. }
       assert (s <= d) as H26. { specialize (H11 s ltac:(auto)). auto. }
       replace d with s by lia. split. destruct H3 as [x2 [y2 H3]]. apply H7; try lia.
       exists x2, y2. lia. exists x, y; lia.
Qed.