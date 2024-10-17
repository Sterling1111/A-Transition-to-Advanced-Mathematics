Require Import ZArith Lia Classical Reals Lra Classical_sets List Fibonacci Sums Sets.
Require Export Chapter13.

Import ListNotations SetNotations.

Open Scope nat_scope.

Lemma lemma_14_1 : forall n : nat,
  n >= 7 -> fact n > 3^n.
Proof.
  intros n H1. induction n as [| k IH]. try lia.
  assert (S k = 7 \/ k >= 7) as [H2 | H2] by lia.
  - rewrite H2. compute; lia.
  - simpl in *. nia.
Qed.

Lemma lemma_14_2 : forall n : nat,
  n >= 6 -> fact n > n^3.
Proof.
  intros n H1. induction n as [| k IH]; try lia.
  - assert (S k = 6 \/ k >= 6) as [H2 | H2] by lia.
    + rewrite H2. compute. lia.
    + rewrite fact_simpl. specialize (IH H2). simpl in *. nia.
Qed.

Lemma lemma_14_3 : forall n : nat,
  3^n >= n^3.
Proof.
  induction n as [| k IH]; try (simpl; nia).
  assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k > 3) as [H1 | [H1 | [H1 | [H1 | H1]]]] by lia; try (subst; simpl; nia).
  replace (3 ^ S k) with (3 ^ k + 3^k + 3^k) by (simpl; lia). replace (S k ^ 3) with (k^3 + 3 * k^2 + 3 * k + 1) by (simpl; lia).
  assert (H2 : 3^k >= k * k^2). { replace (k * k^2) with (k^3) by (simpl; lia). auto. }
  assert (H3 : 3^k >= 3 * k^2). { nia. } assert (H4 : 3^k >= k * k * k). { replace (k * k * k) with (k^3) by (simpl; lia). auto. }
  assert (H5 : 3^k >= 3 * k + 1). { nia. } nia.
Qed.

Lemma lemma_14_4 : forall (l : list Prop),
  ~ (fold_right and True l) <-> fold_right or False (map (fun P => ~ P) l).
Proof.
  intros l; induction l as [| h t IH]; (simpl; tauto).
Qed.

Open Scope R_scope.

Lemma lemma_14_5 : forall (l : list R),
  Rabs (sum_f 0 (length l - 1) (fun i => nth i l 0)) <= sum_f 0 (length l - 1) (fun i => Rabs (nth i l 0)).
Proof.
  induction l as [| h t IH].
  - simpl. repeat rewrite sum_f_0_0; lra.
  - replace (length (h :: t) - 1)%nat with (length t) by (simpl; lia). assert (length t = 0 \/ length t > 0)%nat as [H1 | H1] by lia.
    -- rewrite H1. repeat rewrite sum_f_0_0; solve_abs.
    -- rewrite sum_f_nth_cons_7; try lia. rewrite sum_f_nth_cons_5; try lia. solve_abs.
Qed.

Section section_14_6.

  Import Fibonacci.

  Local Notation F_nat := fibonacci_nat.
  Local Notation F := fibonacci_R.

  Open Scope R_scope.

(* run this command to print out the first 15 fib numbers*)
Compute (map F_nat (seq 0 15)).

  Lemma lemma_14_6_b : forall n : nat,
    sum_f 0 n (fun i => F i) = F (S (S n)) - 1.
  Proof.
    intros n. induction n as [| k IH].
    - rewrite sum_f_0_0. simpl. lra.
    - rewrite sum_f_i_Sn_f; try lia. rewrite IH. repeat rewrite fib_S_S_n. lra.
  Qed.

  Lemma lemma_14_6_c : forall n : nat,
    sum_f 0 n (fun i => (F i)^2) = F n * F (S n).
  Proof.
    induction n as [| k IH].
    - rewrite sum_f_0_0. simpl. lra.
    - rewrite sum_f_i_Sn_f; try lia. rewrite IH. replace (F (S k) ^ 2) with (F (S k) * F (S k)) by lra. 
      repeat rewrite fib_S_S_n. lra.
  Qed.

End section_14_6.

Section section_14_7.
  Import Fibonacci.

  Local Notation F := fibonacci_R.

  Open Scope R_scope.

  Lemma lemma_14_7 : forall n : nat,
    (n >= 13)%nat -> F n > INR (n)^2.
  Proof.
    intros n H1. induction n as [| k IH]; try lia.
    assert (S k = 13 \/ k >= 13)%nat as [H2 | H2] by lia.
    - rewrite H2. compute; lra.
    - specialize (IH H2). rewrite fib_n in IH; try lia. rewrite fib_n; try lia. rewrite fib_n; try lia.
      replace (S k - 1 - 1)%nat with (k - 1)%nat by lia. replace (S k - 2)%nat with (k-1)%nat by lia.
      replace (S k - 1 - 2)%nat with (k - 2)%nat by lia. replace (INR (S k) ^ 2) with (INR k ^ 2 + 2 * INR k + 1).
      2 : { break_INR. simpl. nra. } assert (H3 : F (k - 1) >= F (k - 2)). { apply n1_ge_n2_imp_fib_n1_ge_fib_n2; lia. }
      assert (H4 : F (k - 1) >= (INR k ^ 2) / 2). { nra. } assert (H5 : INR k >= 13). { apply le_INR in H2. simpl in H2; nra. } nra. 
  Qed.
  
End section_14_7.