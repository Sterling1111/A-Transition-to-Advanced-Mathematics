Require Import ZArith Lia Classical Reals Lra Classical_sets List
               Ensembles QArith ClassicalFacts Finite_sets Powerset Finite_sets_facts Image
               Fibonacci Sums Sets Binomial.
Require Export Chapter15.

Import ListNotations SetNotations Choose_Notations.

Open Scope nat_scope.

Lemma lemma_16_1_a : forall n,
  n ∁ 0 = 1 /\ n ∁ n = 1.
Proof.
  split. 
  - apply n_choose_0.
  - apply n_choose_n.
Qed.

Lemma lemma_16_1_b : forall n,
  n > 0 -> n ∁ 1 = n /\ n ∁ (n - 1) = n.
Proof.
  intros n H1. split.
  - apply n_choose_1.
  - replace n with (S (n - 1)) at 1 by lia. rewrite Sn_choose_n. lia.
Qed.

Ltac choose_cases n k H1 H2 :=
  assert (n = k \/ n > k) as [H1 | H1]; assert (k = 0 \/ k > 0) as [H2 | H2] by lia; 
  subst; try rewrite Nat.sub_0_r in *; simpl; try lia.

Lemma lemma_16_2 : forall n k,
  n >= k -> n ∁ k = n ∁ (n - k).
Proof.
  intros n k H1. repeat rewrite n_choose_k_def; try lia.
  replace (n - (n - k)) with k by lia. rewrite Nat.mul_comm. reflexivity.
Qed.

Section section_16_3.
  Open Scope R_scope.

  Let choose := Binomial_R.choose.

  Lemma lemma_16_3 : forall n j k,
    (n >= j)%nat -> (n >= k)%nat -> choose n j * choose (n - j) k = choose n k * choose (n - k) j.
  Proof.
    intros n j k H1 H2. assert (n - k < j \/ n - k >= j)%nat as [H3 | H3] by lia.
    - unfold choose. rewrite Binomial_R.k_gt_n_n_choose_k with (n := (n - k)%nat) (k := j); try lia. rewrite Rmult_0_r.
      rewrite Binomial_R.k_gt_n_n_choose_k with (n := (n - j)%nat) (k := k); try lia. lra.
    - repeat rewrite Binomial_R.n_choose_k_def; try lia. replace (n - j - k)%nat with (n - k - j)%nat by lia.
      field_simplify; try (repeat split; apply not_0_INR; apply fact_neq_0). 
  Qed.

  Open Scope nat_scope.

  Lemma lemma_16_3' : forall n j k,
    n >= j -> n >= k -> n ∁ j * (n - j) ∁ k = n ∁ k * (n - k) ∁ j.
  Proof.
    intros n j k H1 H2. pose proof (lemma_16_3 n j k H1 H2) as H3. repeat rewrite <- Choose_N_eq_Choose_R in H3.
    repeat rewrite <- mult_INR in H3. apply INR_eq in H3. lia.
  Qed.
End section_16_3.

Open Scope R_scope.

Lemma lemma_16_4 : forall n,
  sum_f 0 n (fun k => INR (n ∁ k)) = 2^n.
Proof.
  intros n. pose proof (Binomial_Theorem 1 1 n) as H1. replace (1 + 1) with 2 in H1 by lra.
  rewrite H1. apply sum_f_equiv; try lia. intros k H2. repeat rewrite pow1. lra.
Qed.

Lemma lemma_16_5 : forall n,
  (n > 0)%nat -> sum_f 0 n (fun k => (-1)^k * INR (n ∁ k)) = 0.
Proof.
  intros n H1. pose proof (Binomial_Theorem 1 (-1) n) as H2. replace (1 + -1) with 0 in H2 by lra.
  rewrite pow_i in H2; try lia. rewrite H2. apply sum_f_equiv; try lia. intros k H4. repeat rewrite pow1. lra.
Qed.

(* dont forget that our x is 2x and y is 3y*)
(*Compute ((8 ∁ 3) * 2^5 * 3^3)%nat.*)

Lemma lemma_16_6 : forall x y, (2 * x + 3 * y)^8 = 256 * x ^ 8 + 3072 * x ^ 7 * y + 16128 * x ^ 6 * y ^ 2 + 48384 * x ^ 5 * y ^ 3 + 90720 * x ^ 4 * y ^ 4 + 108864 * x ^ 3 * y ^ 5 + 81648 * x ^ 2 * y ^ 6 + 34992 * x * y ^ 7 + 6561 * y ^ 8.
Proof.
  intros x y. nra. (* simplify_binomial_expansion. reflexivity. will work but until we have fast compute for choose its very slow*)
Qed.

Section section_16_7.
  Let choose := Binomial_R.choose.

  Lemma lemma_16_7 : forall n k,
    (n >= k)%nat -> (k > 0)%nat -> INR k * choose n k = INR n * choose (n - 1) (k - 1).
  Proof.
    intros n k H1 H2. repeat rewrite Binomial_R.n_choose_k_def; try lia. replace (n - 1 - (k - 1))%nat with (n - k)%nat by lia.
    apply Rmult_eq_reg_r with (r := INR (fact (n - k))). 2 : { apply not_0_INR. apply fact_neq_0. }
    field_simplify; try (split; apply not_0_INR; apply fact_neq_0). replace n%nat with (S (n - 1)) at 2 by lia.
    replace (INR (S (n - 1)) * INR (fact (n - 1))) with (INR (fact n)).
    2 : { rewrite <- mult_INR. rewrite <- fact_simpl. replace (S (n - 1)) with n by lia. reflexivity. }
    replace (INR (fact k)) with (INR k * INR (fact (k - 1))) at 1. 
    2 : { rewrite <- mult_INR. replace k with (S (k - 1)) at 1 by lia. rewrite <- fact_simpl. replace (S (k - 1)) with k by lia. reflexivity. }
    field. split. apply not_0_INR. apply fact_neq_0. apply not_0_INR. lia.
  Qed.

  Open Scope nat_scope.

  Lemma lemma_16_7' : forall n k,
    n >= k -> k > 0 -> k * n ∁ k = n * (n - 1) ∁ (k - 1).
  Proof.
    intros n k H1 H2. pose proof (lemma_16_7 n k H1 H2) as H3. repeat rewrite <- Choose_N_eq_Choose_R in H3.
    repeat rewrite <- mult_INR in H3. apply INR_eq in H3. lia.
  Qed.
End section_16_7.

Section section_16_8.

Open Scope nat_scope.

(* run this command to find 2n choose n for n in {0, 1, 2, 3, 4} *)
(* Compute (map (fun n => (2 * n) ∁ n) (seq 0 5)). *)

Lemma lemma_16_7_b : forall n,
  n > 0 -> Nat.Even ((2 * n) ∁ n).
Proof.
  intros n H1. rewrite binomial_recursion_4; try lia.
  replace ((2 * n - 1) ∁ n) with ((2 * n - 1) ∁ (n - 1)).
  2 : { rewrite lemma_16_2; try lia. replace (2 * n - 1 - (n - 1)) with n by lia. reflexivity. }
  exists ((2 * n - 1) ∁ (n - 1)). lia.
Qed.

End section_16_8.

Open Scope nat_scope.

Lemma lemma_16_9_a : forall n k,
  n >= 9 -> n ∁ k < 2 ^ (n-2).
Proof.
  intros n k H1. generalize dependent k. induction n as [|n IH]; try lia.
  intros k. assert (S n = 9 \/ n >= 9) as [H2 | H2] by lia.
  - rewrite H2. simpl. assert (k > 9 \/ k <= 9) as [H3 | H3] by lia.
    -- rewrite n_lt_k_choose_k; lia.
    -- pose proof ((choose_n_max 9 k)) as H4. simpl in H4. pose proof (Z_choose_eq_choose 9 4) as H5.
       replace (Z_choose 9 4) with 126%Z in H5 by (compute; lia). lia.
        (*repeat (destruct k; [compute; lia | try lia]). too slow while we dont have a fast way to compute choose aka proven dp*)
  - assert (k = 0 \/ k >= 1) as [H3 | H3] by lia.
    -- specialize (IH H2). rewrite H3. rewrite n_choose_0. simpl. replace (n - 1) with (S (n - 2)) by lia. rewrite Nat.pow_succ_r'.
       assert (n ∁ 0 < 2 ^ (n - 2)) as H4 by (apply IH). lia.
    -- specialize (IH H2). simpl. replace (S n) with (n + 1) by lia. rewrite binomial_recursion_2; try lia.
       replace (2 ^ (n - 1)) with (2 * 2 ^ (n - 2)). 2 : { replace (n -1) with (S (n - 2)) by lia. simpl. lia. }
       specialize (IH k) as H4. specialize (IH (k - 1)) as H5. lia.
Qed.

Lemma lemma_16_9_b : forall n k,
  n >= 8 -> n ∁ k < fact (n - 3).
Proof.
  intros n k H1. generalize dependent k. induction n as [|n IH]; try lia.
  intros k. assert (S n = 8 \/ n >= 8) as [H2 | H2] by lia.
  - rewrite H2. simpl. assert (k > 8 \/ k <= 8) as [H3 | H3] by lia.
    -- rewrite n_lt_k_choose_k; lia.
    -- assert (8 ∁ k <= 8 ∁ 4) as H4 by apply choose_n_max. pose proof (Z_choose_eq_choose 8 4) as H5.
       replace (Z_choose 8 4) with 70%Z in H5 by (compute; lia). lia.
       (* repeat (destruct k; [compute; lia | try lia]). too slow while we dont have fast choose compute *)
  - assert (k = 0 \/ k >= 1) as [H3 | H3] by lia.
    -- rewrite H3. rewrite n_choose_0. replace (S n - 3) with (S (n - 3)) by lia. simpl. pose proof (fact_geq_1 (n - 3)) as H4. nia.
    -- specialize (IH H2). simpl. replace (S n) with (n + 1) by lia. rewrite binomial_recursion_2; try lia.
       replace (fact (n - 1)) with ((n - 1) * fact (n - 2)). 2 : { replace (n - 1) with (S (n - 2)) by lia. simpl. reflexivity. }
       specialize (IH k) as H4. specialize (IH (k - 1)) as H5. replace (n - 2) with (S (n - 3)) by lia. simpl. nia.
Qed.