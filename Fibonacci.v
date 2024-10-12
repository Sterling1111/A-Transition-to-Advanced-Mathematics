Require Import Reals Lra Lia WI_SI_WO.

Open Scope R_scope.

Fixpoint fibonacci_nat (n : nat) : nat :=
match n with
| O => 1
| S n' => match n' with
          | O => 1
          | S n'' => fibonacci_nat(n') + fibonacci_nat(n'')
          end
end.

Fixpoint fibonacci_R (n : nat) : R :=
match n with
| O => 1
| S n' => match n' with
          | O => 1
          | S n'' => fibonacci_R(n') + fibonacci_R(n'')
          end
end.

Local Notation F_nat := fibonacci_nat.
Local Notation F := fibonacci_R.

Open Scope nat_scope.
Lemma fib_S_S_n_nat : forall n : nat, F_nat (S (S n)) = F_nat (S n) + F_nat n.
Proof. reflexivity. Qed.
Close Scope nat_scope.

Lemma fib_S_S_n : forall n : nat, F (S (S n)) = F (S n) + F n.
Proof.
  reflexivity.
Qed.

Lemma fib_n_plus_2 : forall n : nat, F(n+2) = F(n+1) + F(n).
Proof.
  intro n. 
  replace ( (n + 1)%nat ) with ( S n )%nat by lia.
  replace ( (n + 2)%nat ) with ( S (S n) )%nat by lia.
  apply fib_S_S_n.
Qed.

Lemma fib_n_plus_1 : forall n : nat, (n > 0)%nat -> F(n+1) = F(n) + F(n-1).
Proof.
  intros n H1. destruct n as [| n'] eqn:En.
  - simpl. exfalso. apply (Nat.lt_irrefl) in H1. apply H1.
  - replace ( (S n') ) with ( (n' + 1)%nat ) by lia. 
    rewrite <- Nat.add_assoc. simpl.
    replace ( (n' + 1 - 1)%nat ) with ( n' ) by lia.
    apply fib_n_plus_2.
Qed.

Lemma fib_n_plus_3 : forall n : nat, F(n+3) = F(n+2) + F(n+1).
Proof.
  intro n. 
  replace ( (n + 2)%nat ) with ( (n + 1 + 1)%nat ) by lia.
  replace ( (n + 3)%nat ) with ( (n + 1 + 2)%nat ) by lia.
  apply fib_n_plus_2.
Qed.

Lemma fib_n : forall n, 
  (n > 1)%nat -> F n = F (n - 1) + F (n - 2).
Proof.
  intros n H1. replace n with (S (S (n - 2))) at 1 by lia. 
  replace (n - 1)%nat with (S (n - 2)) by lia. apply fib_S_S_n.
Qed.

Lemma fib_n_ge_1 : forall n, F n >= 1.
Proof.
  intro n. strong_induction n. do 2 (destruct n; try (simpl; lra)).
  assert (H1 : F (S n) >= 1) by (apply IH; lia).
  assert (H2 : F n >= 1) by (apply IH; lia).
  rewrite fib_S_S_n. lra.
Qed.

Lemma fib_n_gt_0 : forall n, F n > 0.
Proof.
  intros n. assert (H1 : F n >= 1) by apply fib_n_ge_1. lra.
Qed.

Lemma fib_Sn_ge_fib_n : forall n : nat,
  F (S n) >= F n.
Proof.
  induction n as [| k IH].
  - simpl. lra.
  - rewrite -> fib_S_S_n.  
    assert (H1 : F (S k) > 0) by apply fib_n_gt_0.
    assert (H2 : F k > 0) by apply fib_n_gt_0.
    lra.
Qed.

Lemma n_ge_1_imp_fib_Sn_gt_fib_n : forall n : nat,
  (n >= 1)%nat -> F (S n) > F n.
Proof.
  intros n H. destruct n as [| n'] eqn:En.
  - lia.
  - rewrite -> fib_S_S_n. 
    assert (H1 : F (S n') > 0) by apply fib_n_gt_0.
    assert (H2 : F n' > 0) by apply fib_n_gt_0.
    lra.
Qed.

Lemma n1_ge_n2_imp_fib_n1_ge_fib_n2 : forall (n1 n2 : nat),
  (n1 >= n2)%nat -> F n1 >= F n2.
Proof.
  intros n1 n2 H.
  induction H.
  - lra.
  - assert (H2 : F (S m) >= F m)  by apply fib_Sn_ge_fib_n.
    lra.
Qed.

Lemma fib_n_ge_n : forall n : nat,
  F n >= INR n.
Proof.
  induction n as [| k IH].
  - simpl. lra.
  - replace ( (S k) ) with ( (k + 1)%nat ) by lia.
    destruct k as [| k'] eqn:Ek.
    -- simpl. lra.
    -- rewrite fib_n_plus_1.
      --- rewrite plus_INR. 
          assert (H1 : F (S k' - 1) >= 1) by apply fib_n_ge_1.
          replace ( (INR 1) ) with ( (1) ) by (simpl; lra). lra.
      --- lia.
Qed.
    
Lemma fib_2n_ge_fib_n : forall n : nat,
  F (2 * n) >= F n.
Proof.
  intros n. assert (H : (2 * n >= n)%nat) by lia.
  apply n1_ge_n2_imp_fib_n1_ge_fib_n2. apply H.
Qed.

Lemma fib_2n_times_fib_n_ge_n : forall n : nat,
  F (2 * n) * F (2 * n - 1) >= F n.
Proof.
  intro n. assert (H1 : F ((2 * n)%nat) > 0) by apply fib_n_gt_0.
  assert (H2 : F ((2 * n - 1)%nat) >= 1) by apply fib_n_ge_1.
  assert (H3 : F ((2 * n)%nat) >= F n) by apply fib_2n_ge_fib_n.
  apply Rmult_ge_compat_l with (r := F (2 * n)%nat) in H2.
  - rewrite Rmult_1_r in H2. lra.
  - apply Rgt_ge. apply H1. 
Qed.

Lemma fib_prod_ge_n : forall (n : nat),
  F (2 * n) * F (2 * n - 1) >= INR n.
Proof.
  intros n. 
  assert (H1 : F (2 * n) * F (2 * n - 1) >= F n) by apply fib_2n_times_fib_n_ge_n.
  assert (H2 : F n >= INR n) by apply fib_n_ge_n.
  apply Rge_trans with (r3 := INR n) in H1.
  - apply H1.
  - apply H2.
Qed.