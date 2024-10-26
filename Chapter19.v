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

Theorem theorem_19_5 : forall a,
  a > 1 -> Znt.prime a <-> (forall b c, (a | b * c) -> (a | b) \/ (a | c)).
Proof.
  intros a H1. split; intros H2.
  - intros b c H3. rewrite Z.mul_comm in H3. pose proof classic (a | b) as [H4 | H4];
    pose proof classic (a | c) as [H5 | H5]; auto. left.
    apply theorem_18_13 with (b := c); auto. apply theorem_19_4; auto.
  - pose proof classic (Znt.prime a) as [H3 | H3]; auto.
    pose proof Znt.not_prime_divide a ltac:(lia) H3 as [b [H4 [c H5]]].
    specialize (H2 b c ltac:(exists 1; lia)). destruct H2 as [H2 | H2];
    apply Z.divide_pos_le in H2; nia.
Qed.

Theorem theorem_19_6 : forall p l,
  Znt.prime p -> (p | fold_right Z.mul 1 l) -> exists x, List.In x l /\ (p | x).
Proof.
  intros p l H1 H2. assert (p > 1) as H3 by (destruct H1; lia). induction l as [| h t IH]; simpl in *.
  - destruct H2 as [x H2]. pose proof Znt.Zmult_one p x ltac:(lia) ltac:(lia); lia.
  - apply theorem_19_5 in H2 as [H4 | H4]; auto.
    -- exists h. split; auto.
    -- specialize (IH H4) as [x [H5 H6]]. exists x. split; auto.
Qed.

Theorem theorem_19_7 : forall z,
  z > 1 -> (exists p, Znt.prime p /\ (p | z)).
Proof.
  intros z. strong_induction z.
  assert (z = 2 \/ z > 2) as [H2 | H2] by lia.
  - exists 2. split; [apply Znt.prime_2 | exists 1; lia].
  - destruct (Znt.prime_dec z) as [H4 | H4].
    -- exists z. split; [auto | exists 1; lia].
    -- rewrite <- Znt.prime_alt in H4. apply not_and_or in H4 as [H4 | H4]; try lia.
       apply not_all_ex_not in H4 as [p H4]. apply imply_to_and in H4 as [H4 H5]. apply NNPP in H5.
       specialize (IH p ltac:(lia) ltac:(lia)). destruct IH as [p' IH]. exists p'. split; try apply IH.
       apply Z.divide_trans with (m := p); tauto.
Qed.

Definition prime_list (l : list Z) : Prop := Forall Znt.prime l.

Lemma fold_right_mul_distributive : forall (k : Z) (l : list Z),
  fold_right Z.mul k l = k * fold_right Z.mul 1 l.
Proof.
  intros k l. induction l as [| h l' IH].
  - simpl. lia.
  - simpl. rewrite IH. lia.
Qed.

Lemma lemma_2_17_a : forall z : Z,
  z > 1 -> exists l : list Z,
    prime_list l /\ z = fold_right Z.mul 1 l.
Proof.
    intros z. strong_induction z.
    - assert (z = 2 \/ z > 2) as [H2 | H2] by lia.
      -- exists [2]. split; try (simpl; lia); try (constructor; auto). apply Znt.prime_2.
      -- destruct (Znt.prime_dec z) as [H3 | H3].
         + exists [z]. split; try (simpl; lia); try constructor; auto.
         + rewrite <- Znt.prime_alt in H3. apply not_and_or in H3 as [H3 | H3]; try lia.
           apply not_all_ex_not in H3 as [p H3]. apply imply_to_and in H3 as [H4 H5].
           apply NNPP in H5 as [k H5].
           assert (exists l1 : list Z, prime_list l1 /\ p = fold_right Z.mul 1 l1) as [l1 H11] by (apply IH; lia).
           assert (exists l2 : list Z, prime_list l2 /\ k = fold_right Z.mul 1 l2) as [l2 H12] by (apply IH; nia).
           exists (l1 ++ l2). split; try (apply Forall_app; split; tauto).
           rewrite fold_right_app. rewrite fold_right_mul_distributive. lia.
Qed.

