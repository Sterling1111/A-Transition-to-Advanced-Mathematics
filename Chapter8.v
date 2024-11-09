Require Import Imports QRT.
Require Export Chapter7.

Open Scope Z_scope.

Lemma lemma_8_1 : forall x y : Z, (Z.Even x <-> Z.Even y) -> Z.Even (x^2 + x * y).
Proof.
    intros x y [H1 H2]. pose proof Z.Even_or_Odd x as [H3 | H3].
    - specialize (H1 H3). apply even_plus_Z. left. split; apply even_mult_Z; auto.
    - apply contra_2 in H2. 2 : { apply not_even_iff_odd_Z; auto. } apply even_plus_Z. right. split.
      -- apply lemma_6_3; auto.
      -- apply odd_mult_Z; auto. apply not_even_iff_odd_Z; auto.
Qed.

Lemma lemma_8_2_a : forall a b c : Z, ~(a | b * c) -> ~(a | b) /\  ~(a | c).
Proof.
    intros a b c H1. apply not_or_and. intros [[k H2]| [k H2]].
    - apply H1. exists (c * k). lia.
    - apply H1. exists (b * k). lia.
Qed.

Lemma ex_not_all_not_3 : forall (U : Type) (P : U -> U -> U -> Prop),
    (exists x y z : U, ~P x y z) -> ~(forall x y z : U, P x y z).
Proof.
    intros U P [x [y [z H1]]] H2. apply H1. apply H2.
Qed.

Lemma lemma_8_2_b : (forall a b c : Z,
    ~(a | b) \/ ~(a | c) -> ~(a | b * c)) -> False.
Proof.
    apply ex_not_all_not_3. exists 6, 2, 3. intros H1. apply H1.
    - apply not_and_or. intros [[k H2] H3]. lia.
    - exists 1. lia.
Qed.

Definition Zmod_equiv (a b n : Z) : Prop := Z.divide n (a - b).

Notation "a ≡ b (mod  n )" := (Zmod_equiv a b n) (at level 70).

Proposition prop_8_13 : forall a b c n : Z,
    a ≡ b (mod n) -> a * c ≡ b * c (mod n).
Proof.
    intros a b c n [k H1]. exists (k * c). lia.
Qed.

Lemma lemma_8_3_a : forall x : Z, x^2 ≡ 0 (mod 4) \/ x^2 ≡ 1 (mod 4).
Proof.
    intros x.
    assert (exists i, x = 2*i \/ x = 2*i + 1) as [i H1] by zforms. repeat destruct H1 as [H1 | H1].
    - rewrite H1. left. unfold Zmod_equiv. unfold Z.divide. exists (i^2). lia.
    - right. exists (i^2 + i). rewrite H1. lia.
Qed.

Lemma lemma_8_3_b : forall x : Z, (4 | x^4 - x^2).
Proof.
    intros x. 
    assert (exists k, x = 2 * k \/ x = 2 * k + 1) as [k [H1 | H1]] by zforms.
    - exists (4 * k^4 - k^2). rewrite H1. lia.
    - exists (4 * k^4 + 8 * k^3 + 5 * k^2 + k). lia.
Qed.

Lemma lemma_8_4_a : forall a b c n : Z, a ≡ b (mod n) -> b ≡ c (mod n) -> a ≡ c (mod n).
Proof.
    intros a b c n [k H1] [j H2]. exists (k + j). lia.
Qed.

Lemma lemma_8_4_b : 11 ≡ -3 (mod 7) -> -3 ≡ 4 (mod 7) -> 11 ≡ 4 (mod 7).
Proof.
    intros H1 H2. apply lemma_8_4_a with (a := 11) (b := -3) (n := 7) (c := 4); auto.
Qed.

Lemma lemma_8_5 : forall n : Z, (3 | n) <-> (3 | n^2).
Proof.
    intros n. split.
    - intros [k H1]. exists (3 * k^2). lia.
    - intros [j H1]. assert (exists k, n = 3 * k \/ n = 3 * k + 1 \/ n = 3 * k + 2) as [k [H2 | [H2 | H2]]] by zforms.
        + exists (k). lia.
        + lia.
        + lia.
Qed.

Lemma lemma_8_6 : forall n : Z, (3 | 2 * n^2 + 1) <-> ~ (3 | n).
Proof.
    intros n. split.
    - intros [j H1] [k H2]. lia.
    - intros H1. assert (exists k, n = 3 * k \/ n = 3 * k + 1 \/ n = 3 * k + 2) as [k [H2 | [H2 | H2]]] by zforms.
        + exfalso. apply H1. exists k. lia.
        + exists (6 * k^2 + 4 * k + 1). lia.
        + exists (6 * k^2 + 8 * k + 3). lia.
Qed.

Lemma lemma_8_7_a : forall a b c d n : Z, a ≡ b (mod n) -> c ≡ d (mod n) -> a * c ≡ b * d (mod n).
Proof.
    intros a b c d n [j H1] [k H2]. unfold Zmod_equiv. exists (a * k + d * j). lia. 
Qed.

(* I guess this means that if a is congruent to b mod n then a^2 is congruent to b^2 mod n*)
Lemma lemma_8_7_b : forall a b n : Z, a ≡ b (mod n) -> a^2 ≡ b^2 (mod n).
Proof.
    intros a b n H1. replace (a^2) with (a * a) by lia. replace (b^2) with (b * b) by lia. apply lemma_8_7_a; auto.
Qed.

Lemma lemma_8_7_c : 19 ≡ 5 (mod 7) -> 19^2 ≡ 5^2 (mod 7).
Proof.
    intros H1. apply lemma_8_7_b; auto.
Qed.

Lemma lemma_8_7_d : forall a b n : Z, a ≡ b (mod n) -> a^3 ≡ b^3 (mod n).
Proof.
    intros a b n H1. replace (a^3) with (a^2 * a) by lia. replace (b^3) with (b^2 * b) by lia. apply lemma_8_7_a; auto. apply lemma_8_7_b; auto.
Qed.

(* Now we see a pattern. havent gotten to induction yet but its easy *)

Lemma lemma_8_7_e : forall (a b n : Z) (m : nat), a ≡ b (mod n) -> a ^ (Z.of_nat m) ≡ b ^ (Z.of_nat m) (mod n).
Proof.
    intros a b n m H1. induction m as [| m' IH].
    - simpl. exists 0. lia.
    - repeat rewrite Nat2Z.inj_succ; repeat rewrite Z.pow_succ_r; try lia. apply lemma_8_7_a; auto.
Qed. 

Open Scope R_scope.

Ltac solve_abs := 
  try intros; repeat unfold Rabs in *; repeat destruct Rcase_abs in *; try nra; try field; try nia.

Lemma lemma_8_8 : forall x y : R, Rabs (x + y) <= Rabs x + Rabs y.
Proof.
    intros x y. unfold Rabs. destruct (Rcase_abs (x + y)) as [H1 | H1].
    - destruct (Rcase_abs x) as [H2 | H2]; destruct (Rcase_abs y) as [H3 | H3]. nra. nra. nra. nra.
    - destruct (Rcase_abs x) as [H2 | H2]; destruct (Rcase_abs y) as [H3 | H3]. nra. nra. nra. nra. 
Qed.

Lemma lemma_8_8' : forall x y : R, Rabs (x * y) = Rabs x * Rabs y.
Proof.
    intros x y. unfold Rabs. destruct (Rcase_abs (x * y)) as [H1 | H1].
    - destruct (Rcase_abs x) as [H2 | H2]; destruct (Rcase_abs y) as [H3 | H3]. nra. nra. nra. nra.
    - destruct (Rcase_abs x) as [H2 | H2]; destruct (Rcase_abs y) as [H3 | H3]. nra. nra. nra. nra.
Qed.

(* showing the power and use of coq *)
Lemma lemma_8_8'' : forall x y : R, Rabs (x - y) <= Rabs x + Rabs y.
Proof. solve_abs. Qed.     

Lemma lemma_8_9_helper : forall a : R, a^2 = 1 -> a = 1 \/ a = -1.
Proof.
    intros a H1. apply Rminus_eq_compat_r with (r := 1) in H1. field_simplify in H1.
    replace (a^2 - 1) with ((a + 1) * (a - 1)) in H1 by ring. destruct (Rmult_integral (a + 1) (a - 1)) as [H2 | H2]. auto.
    - right. lra.
    - left. lra.
Qed.

Lemma lemma_8_9 : forall a : R, (a^2 <= 1 <-> -1 <= a <= 1).
Proof.
    intros a.
    assert (H1 : forall a b c, a < b -> c > 0 -> a * c < b * c) by (intros; nra). 
    assert (H2 : forall a b c, a < b -> c < 0 -> a * c > b * c) by (intros; nra).
    split; intros H3; try split. 
    - destruct H3 as [H3 | H3]. 2 : { apply lemma_8_9_helper in H3. lra. }
      pose proof (Rtotal_order a (-1)) as [H5 | [H5 | H5]]; try lra.
      assert (H6 : a * a > -1 * a). { apply H2. apply H5. lra. } (* lra can finish now but just to show what we have done *)
      assert (H7 : -a < a^2 < 1). { split. lra. apply H3. } assert (H8 : -a < 1) by lra. assert (H9 : -a * -1 > 1 * -1). { apply H2. apply H8. lra. }
      replace (-a * -1) with a in H9 by lra. rewrite Rmult_1_l in H9. apply Rlt_le. apply Rgt_lt. apply H9.
    - destruct H3 as [H3 | H3]. 2 : { apply lemma_8_9_helper in H3. lra. }
      pose proof (Rtotal_order a 0) as [H4 | [H4 | H4]]; try lra. pose proof (Rtotal_order a (1)) as [H5 | [H5 | H5]]; try lra.
      assert (H6 : a * a > 1 * a). { apply H1. apply H5. apply H4. } (* lra can finish now but just to show what we have done *)
      assert (H7 : a < a^2 < 1). { split. lra. apply H3. } assert (H8 : a < 1) by lra.  assert (H9 : -a * -1 > 1 * -1). lra. 
      replace (-a * -1) with a in H9 by lra. rewrite Rmult_1_l in H9. apply Rlt_le. apply Rgt_lt. apply H8.
    - destruct H3 as [H3 H4]. destruct H3 as [H3 | H3]. 2 : { rewrite <- H3. lra. } destruct H4 as [H4 | H4]. 2 : { rewrite H4. lra. }
      pose proof (Rtotal_order a 0) as [H5 | [H5 | H5]]. 2 : { rewrite H5. lra. }
      -- assert (H6 : -a * -a < 1 * -a). { apply H1. lra. lra. } lra.
      -- assert (H6 : a * a < 1 * a). { apply H1. lra. lra. } lra.
Qed.