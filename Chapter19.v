Require Import ZArith Lia Classical Reals Lra Classical_sets List String
               Ensembles QArith ClassicalFacts Finite_sets Powerset Finite_sets_facts Image 
               NArith DecimalString DecimalNat DecimalNat Decimal
               Fibonacci Sums Sets Binomial QRT WI_SI_WO.

Require Export Chapter18.

Import ListNotations SetNotations Choose_Notations.

Open Scope Z_scope.

Module Znt := ZArith.Znumtheory.

Search (Znt.prime).

Definition composite (n : Z) : Prop := (1 < n)%Z /\ ~ Znt.prime n.

Theorem theorem_19_3 : forall a,
  composite a -> exists b c, 1 < b < a /\ 1 < c < a /\ a = b * c.
Proof.
  intros a [H1 H2]. apply Znt.not_prime_divide in H2 as [b [H3 [c H4]]]; auto.
  exists b, c. repeat split; nia.
Qed.

Theorem theorem_19_4 : forall p a,
  Znt.prime p -> ((p | a) -> Z.gcd p a = p) /\ (~(p | a) -> Z.gcd p a = 1).
Proof.
  intros p a H1. split; intros H2.
  - apply Znt.prime_alt in H1 as [H1 _]. apply Z.divide_gcd_iff in H2; lia.
  - destruct (classic (a | p)) as [H3 | H3].
    -- pose proof (Znt.prime_divisors p H1 a H3) as [H4 | [H4 | [H4 | H4]]]; subst.
       * replace (-1) with (-(1)) by lia. rewrite Z.gcd_opp_r. apply Z.gcd_1_r.
       * apply Z.gcd_1_r.
       * exfalso. apply H2; auto.
       * exfalso. apply H2. apply Znt.Zdivide_opp_r. apply Z.divide_refl.
    -- destruct (classic (Z.gcd p a = 1)) as [H4 | H4]; auto. pose proof Z.gcd_nonneg p a as H5. 
       assert (Z.gcd p a = 0 \/ Z.gcd p a > 1) as [H6 | H6]; try lia.
       * apply gcd_0 in H6 as [H6 H7]; subst. exfalso. apply H2. exists 0; lia.
       * pose proof Z.gcd_divide_r p a as H7. apply Znt.prime_alt in H1. destruct H1 as [H0 H1].
         pose proof classic (Z.gcd p a = p) as [H8 | H8].
         + rewrite H8 in H7. tauto.
         + pose proof Z.gcd_divide_l p a as H9. apply Z.divide_pos_le in H9 as H10; try lia. specialize (H1 (Z.gcd p a) ltac:(lia)). tauto.
Qed.

