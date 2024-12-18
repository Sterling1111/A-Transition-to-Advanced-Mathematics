Require Import Imports Reals_util.

Open Scope R_scope.

Notation "'∑' i n f" := (sum_f i n f)
  (at level 45, i at level 0, n at level 0,
   format "'∑'  i  n  f").

Lemma sum_f_R0_f_Sn : forall f n,
  sum_f_R0 f (S n) = sum_f_R0 f n + f (S n).
Proof.
  destruct n; simpl; reflexivity.
Qed.

Lemma sum_f_R0_fSx_n : forall n f,
  sum_f_R0 (fun x => f (S x)) n = sum_f_R0 f (S n) - f 0%nat.
Proof.
  intros. induction n.
  - simpl. lra.
  - simpl. rewrite IHn. rewrite sum_f_R0_f_Sn. lra.
Qed.

Lemma sum_f_R0_fSxplusa_n : forall n a f,
  sum_f_R0 (fun x => f (S (x + a))%nat) n = sum_f_R0 (fun x => f (x + a)%nat) (S n) - f a.
Proof.
  intros n a f.
  induction n as [| k IH].
  - simpl. lra.
  - simpl. rewrite IH. rewrite sum_f_R0_f_Sn. simpl. lra.
Qed.

Lemma sum_f_Pn: forall f i n,
  (i < n)%nat -> sum_f i n f = sum_f i (Nat.pred n) f + f n.
Proof.
  intros. replace (Nat.pred n) with (n-1)%nat by lia. induction n as [| k IH].
  - lia.
  - replace ((S k - 1)%nat) with (k%nat) by lia.
    assert (H2 : (i < k \/ i = k)%nat) by lia. destruct H2 as [H2 | H2].
    -- rewrite IH. 2 : { lia. }
       unfold sum_f. replace ((S k - i)%nat) with ((S (k - i))%nat) by lia.
       rewrite sum_f_R0_f_Sn. replace ((k - i)%nat) with (S (k - 1 - i)%nat) by lia.
       rewrite sum_f_R0_f_Sn. replace ((S (k - 1 - i) + i))%nat with (k%nat) by lia.
       replace ((S (S (k - 1 - i)) + i))%nat with ((S k)%nat) by lia. reflexivity.
    -- rewrite H2. unfold sum_f. replace ((S k - k)%nat) with 1%nat by lia.
       replace ((k - k)%nat) with 0%nat by lia. simpl. lra.
Qed.

Lemma sum_f_Si : forall (f : nat -> R) (i n : nat),
  (i < n)%nat -> sum_f i n f = sum_f (S i) n f + f i.
Proof.
  intros f i n H1.
  replace (S i) with (i+1)%nat by lia.
  unfold sum_f. replace (n - i)%nat with (S (n - i - 1)) by lia.
  rewrite sum_f_R0_f_Sn. replace (S (n - i - 1) + i)%nat with n%nat by lia.
  replace ((fun x : nat => f (x + (i + 1))%nat)) with (fun x : nat => f (S x + i)%nat).
  rewrite sum_f_R0_fSxplusa_n with (a := i%nat). simpl. 
  replace (S (n - (i+1) + i)%nat) with n%nat by lia.
  replace (n - (i+1))%nat with (n - i - 1)%nat by lia. lra.
  apply functional_extensionality. intros x. replace (x + (i + 1))%nat with (S x + i)%nat by lia. lra.
Qed.

Lemma sum_f_i_Sn_f : forall f i n,
  (i <= n)%nat -> sum_f i (S n) f = sum_f i n f + f (S n).
Proof.
  intros f i n H.
  induction n as [| k IH].
  - replace i%nat with 0%nat by lia. unfold sum_f. simpl. lra.
  - assert (H3 : (i = S k \/ i <= k)%nat) by lia. destruct H3 as [H3 | H3].
    -- rewrite H3. unfold sum_f. replace ((S k - S k)%nat) with 0%nat by lia.
       replace ((S (S k) - S k)%nat) with 1%nat by lia. simpl. lra.
    -- rewrite IH. 2 : { lia. } unfold sum_f. replace ((S (S k) - i)%nat) with (S (S k - i)%nat) by lia.
       rewrite sum_f_R0_f_Sn. replace (S k - i)%nat with (S (k - i))%nat by lia.
       rewrite sum_f_R0_f_Sn. replace ((S (k - i) + i)%nat) with (S k)%nat by lia. 
       replace (S (S (k - i)) + i)%nat with (S (S k))%nat by lia. reflexivity.
Qed.

Lemma sum_f_Si_n_f : forall (f : nat -> R) (i n : nat),
  (i < n)%nat -> sum_f (S i) n f = sum_f i n f - f i.
Proof.
  intros f i n H.
  unfold sum_f.
  induction n as [| k IH].
  - lia.
  - assert (H2 : (i < k \/ i = k)%nat) by lia. destruct H2 as [H2 | H2].
    -- replace ((S k - i)%nat) with (S(k - i)%nat) by lia.
       rewrite sum_f_R0_f_Sn. replace ((S (k - i) + i)%nat) with ((S k)%nat) by lia.
       replace (sum_f_R0 (fun x : nat => f (x + i)%nat) (k - i) + f (S k) - f i)
       with (sum_f_R0 (fun x : nat => f (x + i)%nat) (k - i) - f i + f (S k)) by lra. rewrite <- IH.
       2 : { lia. } replace ((S k - S i)%nat) with (S (k - S i)%nat) by lia. rewrite sum_f_R0_f_Sn.
       replace ((S (k - S i) + S i)%nat) with ((S k)%nat) by lia. reflexivity.
    -- rewrite H2. replace ((S k - k)%nat) with 1%nat by lia. replace ((S k - S k)%nat) with 0%nat by lia.
       simpl. lra.
Qed.


Lemma sum_f_0_0 : forall f,
  sum_f 0 0 f = f 0%nat.
Proof.
  intros. unfold sum_f. simpl. lra.
Qed.

Lemma sum_f_n_0 : forall f n,
  sum_f n 0 f = f n%nat.
Proof.
  intros. unfold sum_f. simpl. reflexivity.
Qed.

Lemma sum_f_n_n : forall f n,
  sum_f n n f = f n.
Proof.
  intros. unfold sum_f. rewrite Nat.sub_diag. simpl. lra.
Qed.

Lemma sum_f_Sn_n : forall n1 n2 f,
  (n1 > n2)%nat -> sum_f n1 n2 f = f n1%nat.
Proof.
  intros. unfold sum_f. replace (n2 - n1)%nat with 0%nat by lia.
  unfold sum_f_R0. simpl. reflexivity.
Qed.

Ltac sum_simpl :=
  first [ rewrite sum_f_i_Sn_f; try lia; sum_simpl
        | rewrite sum_f_n_n 
        | rewrite sum_f_Sn_n; try lia ]; 
  simpl; field_simplify.

Lemma sum_f_const : forall c i n,
  sum_f i n (fun _ => c) = c * INR (n - i + 1)%nat.
Proof.
  intros. induction n as [| k IH].
  - unfold sum_f. simpl. lra.
  - assert (H: (i < k)%nat \/ (i = k)%nat \/ (i > k)%nat) by lia. destruct H as [H | [H | H]].
    -- repeat rewrite sum_f_i_Sn_f. 2 : { lia. } rewrite IH. repeat rewrite plus_INR. repeat rewrite minus_INR; try lia. 
       rewrite S_INR with (n := k). lra.
    -- rewrite H. unfold sum_f. replace (S k - k)%nat with 1%nat by lia. simpl. lra.
    -- assert (H2 : (i > S k)%nat \/ (i = S k)%nat) by lia. destruct H2 as [H2 | H2].
       --- rewrite sum_f_Sn_n. 2 : { lia. } replace (S k - i + 1)%nat with 1%nat by lia. simpl. lra.
       --- rewrite <- H2. repeat rewrite sum_f_n_n. replace (i - i + 1)%nat with 1%nat by lia. simpl. lra.
Qed.

Lemma r_mult_sum_f_i_n_f :
  forall f i n r,
    r * (sum_f i n f) = sum_f i n (fun i => f i * r).
Proof.
  intros. unfold sum_f.
  set (k := (n - i)%nat).
  induction k as [| k' IH].
  - simpl. lra.
  - simpl. rewrite <- IH. lra. 
Qed.

Lemma r_mult_sum_f_i_n_f_l : 
  forall f i n r,
    r * (sum_f i n f) = sum_f i n (fun i => r * f i).
Proof.
  intros. unfold sum_f.
  set (k := (n - i)%nat).
  induction k as [| k' IH].
  - simpl. lra.
  - simpl. rewrite <- IH. lra.
Qed.

Lemma sum_f_sum :
  forall f g i n, 
    sum_f i n f + sum_f i n g = sum_f i n (fun x : nat => f x + g x).
Proof.
  intros. induction n as [| k IH].
  - unfold sum_f. simpl. reflexivity.
  - assert (H: (i < k)%nat \/ (i = k)%nat \/ (i > k)%nat) by lia. destruct H as [H | [H | H]].
    -- repeat rewrite sum_f_i_Sn_f. 2 : { lia. } 2 : { lia. } 2 : { lia. }
       replace (sum_f i k f + f (S k) + (sum_f i k g + g (S k))) with (sum_f i k f + sum_f i k g + f (S k) + g (S k)) by lra.
       rewrite IH. lra.
    -- rewrite H. unfold sum_f. replace (S k - k)%nat with 1%nat by lia. simpl. lra.
    -- assert (H2 : (i > S k)%nat \/ (i = S k)%nat) by lia. destruct H2 as [H2 | H2].
       --- repeat rewrite sum_f_Sn_n. 2 : { lia. } 2 : { lia. } 2 : { lia. } lra.
       --- rewrite <- H2. repeat rewrite sum_f_n_n. lra.
Qed.

Lemma sum_f_congruence: forall (f1 f2 : nat -> R) (i n : nat),
(i <= n)%nat ->
(forall k, (i <= k <= n)%nat -> f1 k = f2 k) ->
sum_f i n f1 = sum_f i n f2.
Proof.
  intros f1 f2 i n H1 H2.
  unfold sum_f. induction n as [| n' IH].
  - simpl. apply H2. lia.
  - assert (H3 : (i = S n')%nat \/ (i < S n')%nat) by lia. destruct H3 as [H3 | H3].
    -- replace (S n' - i)%nat with 0%nat by lia. simpl. rewrite H2.
       2 : { lia. } reflexivity.
    -- replace (S n' - i)%nat with (S (n' - i)%nat) by lia. repeat rewrite sum_f_R0_f_Sn.
       rewrite IH. 2 : { lia. } rewrite H2. 2 : { lia. } reflexivity. intros k H4. apply H2. lia.
Qed.

Lemma sum_f_congruence_le : forall (f1 f2 : nat -> R) (i n : nat),
  (i <= n)%nat ->
  (forall k, (i <= k <= n)%nat -> f1 k <= f2 k) ->
  sum_f i n f1 <= sum_f i n f2.
Proof.
  intros f1 f2 i n H1 H2. unfold sum_f. induction n as [| n' IH].
  - simpl. apply H2. lia.
  - assert (H3 : (i = S n')%nat \/ (i < S n')%nat) by lia. destruct H3 as [H3 | H3].
    -- replace (S n' - i)%nat with 0%nat by lia. simpl. apply H2. lia.
    -- replace (S n' - i)%nat with (S (n' - i)%nat) by lia. repeat rewrite sum_f_R0_f_Sn.
       replace (S (n' - i) + i)%nat with (S n')%nat by lia. assert (f1 (S n') <= f2 (S n')) as H4.
       { apply H2. lia. } apply Rplus_le_compat. apply IH. lia. intros k H5. apply H2. lia. apply H4.
Qed.

Lemma sum_f_nonneg : forall f i n,
  (i <= n)%nat ->
  (forall k, (i <= k <= n)%nat -> 0 <= f k) -> 0 <= sum_f i n f.
Proof.
  intros f i n H1 H2. unfold sum_f. induction n as [| n' IH].
  - simpl. apply H2. lia.
  - assert (H3 : (i = S n')%nat \/ (i < S n')%nat) by lia. destruct H3 as [H3 | H3].
    -- replace (S n' - i)%nat with 0%nat by lia. simpl. apply H2. lia.
    -- replace (S n' - i)%nat with (S (n' - i)%nat) by lia. repeat rewrite sum_f_R0_f_Sn.
       rewrite IH; try lia. replace (S (n' - i) + i)%nat with (S n')%nat by lia. assert (0 <= f (S n')) as H4.
       { apply H2. lia. } lra. intros k H5. apply H2. lia.
Qed.

Lemma sum_f_pos : forall f i n,
  (i <= n)%nat ->
  (forall k, (i <= k <= n)%nat -> 0 < f k) -> 0 < sum_f i n f.
Proof.
  intros f i n H1 H2. unfold sum_f. induction n as [| n' IH].
  - simpl. apply H2. lia.
  - assert (H3 : (i = S n')%nat \/ (i < S n')%nat) by lia. destruct H3 as [H3 | H3].
    -- replace (S n' - i)%nat with 0%nat by lia. simpl. apply H2. lia.
    -- replace (S n' - i)%nat with (S (n' - i)%nat) by lia. repeat rewrite sum_f_R0_f_Sn.
       rewrite IH; try lia. replace (S (n' - i) + i)%nat with (S n')%nat by lia. assert (0 < f (S n')) as H4.
       { apply H2. lia. } lra. intros k H5. apply H2. lia.
Qed.

Lemma sum_f_le : forall f i n r,
  (i <= n)%nat ->
  (forall k, (i <= k <= n)%nat -> f k <= r) -> sum_f i n f <= r * INR (n - i + 1).
Proof.
  intros f i n r H1 H2. unfold sum_f. induction n as [| n' IH].
  - simpl. rewrite Rmult_1_r. apply H2. lia.
  - assert ((i = S n')%nat \/ (i < S n')%nat) as [H3 | H3] by lia.
    -- replace (S n' - i)%nat with 0%nat by lia. simpl. rewrite Rmult_1_r. apply H2. lia.
    -- replace (S n' - i)%nat with (S (n' - i)%nat) by lia. repeat rewrite sum_f_R0_f_Sn. replace (INR (S (n' - i) + 1)) with (INR (n' - i + 1) + 1).
       2 : { repeat rewrite plus_INR. rewrite <- S_INR. reflexivity. }
       rewrite Rmult_plus_distr_l. rewrite Rmult_1_r. apply Rplus_le_compat. apply IH; try lia. intros k H4. apply H2; try lia. apply H2. lia.
Qed.

Lemma sum_f_lt : forall f i n r,
  (i <= n)%nat -> (exists k, (i <= k <= n)%nat /\ f k < r) -> 
  (forall k, (i <= k <= n)%nat -> f k <= r) -> sum_f i n f < r * INR (n - i + 1).
Proof.
  intros f i n r H1 [k [H2 H3]] H4. induction n as [| n' IH].
  - rewrite sum_f_n_0. replace i with k by lia. replace (0 - k + 1)%nat with 1%nat by lia. rewrite Rmult_1_r. apply H3.
  - assert ((i = S n')%nat \/ (i < S n')%nat) as [H5 | H5] by lia.
    -- rewrite <- H5. rewrite sum_f_n_n. replace i with k by lia. replace (k - k + 1)%nat with 1%nat by lia. rewrite Rmult_1_r. apply H3. 
    -- rewrite sum_f_i_Sn_f; try lia. assert (f (S n') <= r) as [H6 | H6] by (apply H4; lia).
       + replace (S n' - i + 1)%nat with ((n' - i + 1) + 1)%nat by lia. rewrite plus_INR. rewrite Rmult_plus_distr_l.
         rewrite Rmult_1_r. apply Rplus_le_lt_compat. apply sum_f_le; try lia. intros j H7. apply H4; try lia. apply H6.
       + assert (k = S n' \/ k < S n')%nat as [H7 | H7] by lia.
         * replace (S n' - i + 1)%nat with ((n' - i + 1) + 1)%nat by lia. rewrite plus_INR. rewrite Rmult_plus_distr_l.
           rewrite Rmult_1_r. rewrite <- H7. apply Rplus_le_lt_compat. apply sum_f_le; try lia. intros j H8. apply H4; try lia. apply H3.
         * replace (S n' - i + 1)%nat with ((n' - i + 1) + 1)%nat by lia. rewrite plus_INR. rewrite Rmult_plus_distr_l.
           rewrite Rmult_1_r. apply Rplus_lt_le_compat. apply IH; try lia. intros j H8. apply H4; try lia. apply Req_le. apply H6.
Qed.

Lemma sum_f_pos' : forall f i n,
  (i <= n)%nat ->
  (forall k, (i <= k <= n)%nat -> 0 <= f k) -> (exists k, (i <= k <= n)%nat /\ 0 < f k) -> 0 < sum_f i n f.
Proof.
  intros f i n H1 H2 H3. induction n as [| n' IH].
  - rewrite sum_f_n_0. destruct H3 as [k [H4 H5]]. replace i with k by lia. apply H5.
  - assert ((i = S n')%nat \/ (i < S n')%nat) as [H4 | H4] by lia.
    -- rewrite <- H4. rewrite sum_f_n_n. destruct H3 as [k [H5 H6]]. replace i with k by lia. apply H6.
    -- rewrite sum_f_i_Sn_f; try lia. assert (0 <= f (S n')) as [H5 | H5] by (apply H2; lia).
       + assert (H6 : 0 <= sum_f i n' f). { apply sum_f_nonneg; try lia. intros k H6. apply H2. lia. } lra.
       + destruct H3 as [k [H6 H7]]. assert (k = S n' \/ k < S n')%nat as [H8 | H8] by lia.
         * rewrite <- H8 in H5. lra.
         * rewrite <- H5. rewrite Rplus_0_r. apply IH; try lia. intros k2 H9. apply H2. lia. exists k; split. lia. lra.
Qed.

Theorem sum_f_equiv : forall (i n : nat) (f1 f2 : nat -> R),
  (i <= n)%nat ->
  (forall k : nat, (i <= k <= n )%nat -> f1 k = f2 k) ->
    sum_f i n f1 = sum_f i n f2.
Proof.
  intros i n f1 f2 H1 H2.
  apply sum_f_congruence. apply H1. apply H2.
Qed.

Theorem sum_f_reindex : forall (f : nat -> R) (i n s : nat),
  (s <= i <= n)%nat ->
  sum_f i n f = sum_f (i - s) (n - s) (fun x => f (x + s)%nat).
Proof.
  intros f i n s H.
  induction i as [| i' IH].
  - simpl. replace ((s)%nat) with (0%nat) by lia. rewrite Nat.sub_0_r.
    apply sum_f_congruence. lia. intros k. replace ((k + 0)%nat) with (k%nat) by lia. reflexivity.
  - assert (H2 : (S i' = n)%nat \/ (S i' < n)%nat) by lia. destruct H2 as [H2 | H2].
    -- rewrite H2. repeat rewrite sum_f_n_n. replace ((n - s + s)%nat) with ((n)%nat) by lia. reflexivity.
    -- rewrite sum_f_Si_n_f. 2 : { lia. }
       assert (H3 : (s <= i')%nat \/ (s = S i')) by lia. destruct H3 as [H3 | H3].
       --- rewrite IH. 2 : { lia. }
            replace ((S i' - s)%nat) with (S (i' - s)%nat) by lia.
            rewrite sum_f_Si_n_f. 2 : { lia. }
            replace ((i' - s + s)%nat) with ((i')%nat) by lia. lra.
       --- rewrite <- H3. replace ((S i' - S i')%nat) with (0%nat) by lia. simpl.
           unfold sum_f. replace ((n - s - (s - s))%nat) with ((n - s)%nat) by lia.
           replace ((n - i')%nat) with (S (n - s)%nat) by lia.
           rewrite sum_f_R0_f_Sn. simpl. replace ((S (n - s + i')%nat)) with n%nat by lia.
           set (f2 := fun x : nat => f (S (x + i'))%nat).
           replace (fun x : nat => f (x + (s - s) + s)%nat) with (fun x : nat => f (S x + i')%nat).
           2 : { apply functional_extensionality. intros x. replace (x + (s - s) + s)%nat with (x + S i')%nat by lia.
           replace (S x + i')%nat with (x + S i')%nat by lia. reflexivity. }
           replace (fun x : nat => f (S x + i')%nat) with f2. 2 : { apply functional_extensionality. unfold f2. simpl. reflexivity. }
           unfold f2. rewrite sum_f_R0_fSxplusa_n. simpl. replace (S (n - s + i')%nat) with n%nat by lia. lra.
Qed.

Theorem sum_f_reindex' : forall (f : nat -> R) (i n s : nat),
  sum_f i n f = sum_f (i + s) (n + s) (fun x => f (x - s)%nat).
Proof.
  intros f i n s.
  induction i as [| i' IH].
  - simpl. unfold sum_f. replace (fun x : nat => f (x + s - s)%nat) with (fun x : nat => (f x%nat)).
    2 : { apply functional_extensionality. intros x. replace (x + s - s)%nat with x%nat by lia. reflexivity. }
    replace (n + s - s)%nat with n%nat by lia. 
    replace (fun x : nat => f (x + 0)%nat) with (fun x : nat => (f x)).
    2 : { apply functional_extensionality. intro x. rewrite Nat.add_0_r. reflexivity. }
    rewrite Nat.sub_0_r. reflexivity.
  - replace (S i' + s)%nat with (S (i' + s)) by lia.
    assert (H2 : (i' < n)%nat \/ (i' = n)%nat \/ (i' > n)%nat) by lia. destruct H2 as [H2 | [H2 | H2]].
    -- rewrite sum_f_Si_n_f. 2 : { lia. } rewrite sum_f_Si_n_f. 2 : { lia. } rewrite IH.
       replace (i' + s - s)%nat with (i')%nat by lia. reflexivity.
    -- rewrite H2. rewrite sum_f_Sn_n by lia. rewrite sum_f_Sn_n by lia. replace ((S (n + s) - s)%nat) with (S n) by lia.
       reflexivity.
    -- repeat rewrite sum_f_Sn_n by lia. replace (S (i' + s) - s)%nat with (S i') by lia.
       reflexivity.
Qed.

Lemma sum_f_mult : forall l1 l2 m n (f g : nat -> R),
  (l1 <= m)%nat -> (l2 <= n)%nat ->
  sum_f l1 m (fun i => f i) * sum_f l2 n (fun i => g i) = sum_f l1 m (fun i => sum_f l2 n (fun j => f i * g j)).
Proof.
  intros l1 l2 m n f g H1 H2. 
   induction m as [| k IH].
  - destruct l1. repeat sum_simpl. rewrite r_mult_sum_f_i_n_f. apply sum_f_equiv; try lia. intros k H. lra.
    repeat rewrite sum_f_Sn_n; try lia.
  - assert ((l1 = S k)%nat \/ (l1 <= k)%nat) as [H3 | H3] by lia.
    -- rewrite <- H3. repeat sum_simpl. rewrite r_mult_sum_f_i_n_f. apply sum_f_equiv; try lia. intros k0 H. lra.
    -- pose proof H3 as H4. apply IH in H3. assert ((l1 = k)%nat \/ (l1 < k)%nat) as [H5 | H5] by lia.
       --- rewrite H5. repeat rewrite sum_f_i_Sn_f; try lia. rewrite H5 in H3. rewrite <- H3.
           replace (fun j : nat => f (S k) * g j) with (fun j : nat => g j * f (S k)) by (apply functional_extensionality; intros; lra).
           rewrite <- r_mult_sum_f_i_n_f. rewrite Rmult_plus_distr_r. reflexivity.
       --- repeat rewrite sum_f_i_Sn_f; try lia. rewrite <- H3.
           replace (fun j : nat => f (S k) * g j) with (fun j : nat => g j * f (S k)) by (apply functional_extensionality; intros; lra).
           rewrite <- r_mult_sum_f_i_n_f. rewrite Rmult_plus_distr_r. reflexivity.
Qed.

Lemma sum_f_plus : forall l n (f g : nat -> R),
  (l <= n)%nat -> sum_f l n f + sum_f l n g = sum_f l n (fun i => f i + g i).
Proof.
  intros l n f g H1. induction n as [| k IH].
  - compute; lra.
  - assert ((l = S k)%nat \/ (l <= k)%nat) as [H2 | H2] by lia.
    -- rewrite <- H2. repeat rewrite sum_f_n_n. unfold sum_f. simpl. lra.
    -- repeat rewrite sum_f_i_Sn_f; try lia. rewrite <- IH; try lia. lra.
Qed.

Lemma sum_f_minus : forall l n (f g : nat -> R),
  (l <= n)%nat -> sum_f l n f - sum_f l n g = sum_f l n (fun i => f i - g i).
Proof.
  intros l n f g H1. induction n as [| k IH].
  - compute; lra.
  - assert ((l = S k)%nat \/ (l <= k)%nat) as [H2 | H2] by lia.
    -- rewrite <- H2. repeat rewrite sum_f_n_n. unfold sum_f. simpl. lra.
    -- repeat rewrite sum_f_i_Sn_f; try lia. rewrite <- IH; try lia. lra.
Qed.

Lemma sum_swap : forall l1 l2 n1 n2 (f : nat -> nat -> R),
  (l1 <= n1)%nat -> (l2 <= n2)%nat ->
  sum_f l1 n1 (fun i => sum_f l2 n2 (fun j => f i j)) = sum_f l2 n2 (fun j => sum_f l1 n1 (fun i => f i j)).
Proof.
  intros l1 l2 n1 n2 f H1 H2. induction n1 as [| k1 IH].
  - replace l1 with 0%nat by lia. repeat rewrite sum_f_0_0. replace (fun j => sum_f 0 0 (fun i => f i j)) with (fun j => f 0%nat j).
    2 : { apply functional_extensionality. intros j. rewrite sum_f_0_0. reflexivity. } reflexivity.
  - assert (l1 = S k1 \/ l1 <= k1)%nat as [H3 | H3] by lia.
    -- rewrite H3. rewrite sum_f_n_n. apply sum_f_equiv; auto. intros k H4. rewrite sum_f_n_n. reflexivity.
    -- rewrite sum_f_i_Sn_f; auto. pose proof H3 as H4. apply IH in H3. rewrite H3. replace ((fun j : nat => sum_f l1 (S k1) (fun i : nat => f i j)))
       with ((fun j => sum_f l1 k1 (fun i => f i j) + f (S k1) j)).
       2 : { apply functional_extensionality. intros x. rewrite sum_f_i_Sn_f; auto. }
       rewrite <- sum_f_plus; auto.
Qed.

Lemma sum_f_nth : forall (l1 : list (list R)) (l2 : list R) (i : nat),
  nth i l2 0 + sum_f 0 (length l1 - 1) (fun j : nat => nth i (nth j l1 []) 0) = sum_f 0 (S (length l1 - 1)) (fun j : nat => nth i (nth j ([l2] ++ l1) []) 0).
Proof.
  intros l1 l2 i. assert (length l1 = 0 \/ length l1 > 0)%nat as [H1 | H1] by lia.
  - rewrite length_zero_iff_nil in H1. rewrite H1. simpl. rewrite sum_f_0_0. rewrite sum_f_Si; try lia. rewrite sum_f_n_n. lra.
  - rewrite sum_f_Si with (n := S (length l1 - 1)). 2 : { simpl. lia. } 
    replace (sum_f 1 (S (length l1 - 1)) (fun j : nat => nth i (nth j ([l2] ++ l1) []) 0)) with (sum_f 1 (S (length l1 - 1)) (fun j : nat => nth i (nth (j-1) l1 []) 0)).
    2 : { apply sum_f_congruence. 2 : { intros k H2. destruct k; simpl; try lia. rewrite Nat.sub_0_r. reflexivity. } lia. }
    replace (nth i (nth 0 ([l2] ++ l1) []) 0) with (nth i l2 0). 2 : { reflexivity. } rewrite sum_f_reindex with (s := 1%nat) (i := 1%nat). 2 : { simpl. lia. }
    replace (S (length l1 - 1)) with (length l1) by lia. replace (1-1)%nat with 0%nat by lia. replace ((fun x : nat => nth i (nth (x + 1 - 1) l1 []) 0)) with (fun x : nat => nth i (nth x l1 []) 0).
    2 : { apply functional_extensionality. intros x. replace (x + 1 - 1)%nat with x by lia. reflexivity. } lra.
Qed.

Lemma sum_f_nth_cons_0 : forall (l : list R) (r : R),
  (length l > 0)%nat -> sum_f 1 (length l) (fun i => nth i (r :: l) 0) = sum_f 0 (length l - 1) (fun i => nth i l 0).
Proof.
  intros l r H1. rewrite sum_f_reindex' with (s := 1%nat) (i := 0%nat). replace (length l - 1 + 1)%nat with (length l) by lia.
  apply sum_f_equiv; try lia. intros k H2. replace (r :: l) with ([r] ++ l) by reflexivity. rewrite app_nth2; try (simpl; lia). simpl. lra.
Qed.

Lemma sum_f_nth_cons_1 : forall {A : Type} (l : list R) (r : R) (f : R -> A -> R) (a : A),
  (length l > 0)%nat -> sum_f 0 (length l) (fun i => f (nth i (r :: l) 0) a) = f r a + sum_f 0 (length l - 1) (fun i => f (nth i l 0) a).
Proof.
  intros A l r f a H1.
  rewrite sum_f_Si with (n := length l); try lia. replace (sum_f 1 (length l) (fun i : nat => f (nth i (r :: l) 0) a)) with (sum_f 0 (length l - 1) (fun i => f (nth i l 0) a)).
  2 : { rewrite sum_f_reindex' with (s := 1%nat) (i := 0%nat). replace (length l - 1 + 1)%nat with (length l) by lia. apply sum_f_equiv; try lia. intros k H2. replace (r :: l) with ([r] ++ l) by reflexivity. rewrite app_nth2; try (simpl; lia). simpl. lra. }
  simpl. lra.
Qed.

Lemma sum_f_nth_cons_2 : forall {A : Type} (l : list R) (r : R) (f : R -> A -> R) (a : A),
  (length l > 0)%nat -> sum_f 1 (length l) (fun i => f (nth i (r :: l) 0) a) = sum_f 0 (length l - 1) (fun i => f (nth i l 0) a).
Proof.
  intros A l r f a H1.
  rewrite sum_f_reindex' with (s := 1%nat) (i := 0%nat). replace (length l - 1 + 1)%nat with (length l) by lia. apply sum_f_equiv; try lia. intros k H2. replace (r :: l) with ([r] ++ l) by reflexivity. rewrite app_nth2; try (simpl; lia). simpl. lra.
Qed.

Lemma sum_f_nth_cons_3 : forall (l1 l2 : list R) (r1 r2 : R),
  (length l1 = length l2)%nat -> sum_f 1 (length l1) (fun i => (r1 * nth i (r2 :: l2) 0 - r2 * nth i (r1 :: l1) 0)^2) = sum_f 0 (length l1 - 1) (fun i => (r1 * nth i l2 0 - r2 * nth i l1 0)^2).
Proof.
  intros l1 l2 r1 r2 H1. rewrite sum_f_reindex' with (s := 1%nat) (i := 0%nat). assert (length l1 = 0 \/ length l1 > 0)%nat as [H2 | H2] by lia.
  - rewrite H2. simpl. rewrite sum_f_Sn_n; try lia. rewrite sum_f_n_n. simpl. lra.
  - replace (length l1 - 1 + 1)%nat with (length l1) by lia. apply sum_f_equiv; try lia. intros k H3. replace (r1 :: l1) with ([r1] ++ l1) by reflexivity. replace (r2 :: l2) with ([r2] ++ l2) by reflexivity. rewrite app_nth2; try (simpl; lia). rewrite app_nth2; try (simpl; lia). simpl. lra.
Qed.

Lemma sum_f_nth_cons_4 : forall (l1 l2 : list R) (r1 r2 : R),
  (length l1 = length l2)%nat -> sum_f 1 (length l1) (fun i => (r1 * nth i (r2 :: l2) 0) ^ 2 - r1 * r2 * nth i (r1 :: l1) 0 * nth i (r2 :: l2) 0) = sum_f 0 (length l1 - 1) (fun i => ((r1 * nth i l2 0) ^ 2 - r1 * r2 * nth i l1 0 * nth i l2 0)).
Proof.
  intros l1 l2 r1 r2 H1. rewrite sum_f_reindex' with (s := 1%nat) (i := 0%nat). assert (length l1 = 0 \/ length l1 > 0)%nat as [H2 | H2] by lia.
  - rewrite H2. simpl. rewrite sum_f_Sn_n; try lia. rewrite sum_f_n_n. simpl. lra.
  - replace (length l1 - 1 + 1)%nat with (length l1) by lia. apply sum_f_equiv; try lia. intros k H3. replace (r1 :: l1) with ([r1] ++ l1) by reflexivity. replace (r2 :: l2) with ([r2] ++ l2) by reflexivity. rewrite app_nth2; try (simpl; lia). rewrite app_nth2; try (simpl; lia). simpl. lra.
Qed.

Lemma sum_f_nth_cons_5 : forall (l : list R) (r : R),
  (length l > 0)%nat -> sum_f 0 (length l) (fun i => nth i (r :: l) 0) = r + sum_f 0 (length l - 1) (fun i => nth i l 0).
Proof.
  intros l r H1. rewrite sum_f_Si; auto. rewrite sum_f_nth_cons_0; auto. simpl. lra.
Qed.

Lemma sum_f_nth_cons_6 : forall (l : list R) (r : R) (f : R -> R),
  (length l > 0)%nat -> sum_f 1 (length l) (fun i => f (nth i (r :: l) 0)) = sum_f 0 (length l - 1) (fun i => f (nth i l 0)).
Proof.
  intros l r f H1.
  rewrite sum_f_reindex' with (s := 1%nat) (i := 0%nat). replace (length l - 1 + 1)%nat with (length l) by lia. apply sum_f_equiv; try lia. intros k H2. replace (r :: l) with ([r] ++ l) by reflexivity. rewrite app_nth2; try (simpl; lia). simpl. lra.
Qed.

Lemma sum_f_nth_cons_7 : forall (l : list R) (r : R) (f : R -> R),
  (length l > 0)%nat -> sum_f 0 (length l) (fun i => f (nth i (r :: l) 0)) = f r + sum_f 0 (length l - 1) (fun i => f (nth i l 0)).
Proof.
  intros l r f H1.
  rewrite sum_f_Si; try lia. rewrite sum_f_nth_cons_6; try lia. simpl. lra.
Qed.

Lemma sum_f_nth_cons_8 : forall (l : list R) (r : R) (f : nat -> R),
  (length l > 0)%nat -> sum_f 0 (length l) (fun i => (nth i (r :: l) 0) * f i) = f 0%nat * r + sum_f 0 (length l - 1) (fun i => nth i l 0 * f (i + 1)%nat).
Proof.
  intros l r f H1.
  rewrite sum_f_Si; try lia. rewrite sum_f_reindex' with (s := 1%nat) (i := 0%nat). replace (length l - 1 + 1)%nat with (length l) by lia.
  replace (nth 0 (r :: l) 0) with r by reflexivity. rewrite Rmult_comm. rewrite Rplus_comm. apply Rplus_eq_compat_l with (r := f 0%nat * r).
  apply sum_f_equiv; try lia. intros k H2. replace (r :: l) with ([r] ++ l) by reflexivity. rewrite app_nth2; try (simpl; lia). simpl.
  replace (k - 1 + 1)%nat with k by lia. reflexivity.
Qed.

Lemma exists_max_of_sequence_on_interval : forall (a : nat -> R) (i j : nat),
  (i <= j)%nat -> exists n : nat, (i <= n <= j)%nat /\ forall m : nat, (i <= m <= j)%nat -> a m <= a n.
Proof.
  intros a i j H1. induction j.
  - assert (i = 0)%nat by lia. subst. exists 0%nat. split; try lia.
    intros m H2. replace m with 0%nat by lia. lra.
  - assert (i = S j \/ i <= j)%nat as [H2 | H2] by lia.
    -- subst. exists (S j). split; try lia. intros m H3. replace m with (S j) by lia. lra.
    -- specialize (IHj H2) as [n [H3 H4]]. assert (a (S j) >= a n \/ a (S j) < a n) as [H5 | H5] by lra.
       + exists (S j). split; try lia. intros m H6. specialize (H4 m). assert (m = S j \/ m <= j)%nat as [H7 | H7] by lia;
         subst; try lra. specialize (H4 ltac:(lia)). lra.
       + exists n. split; try lia. intros m H6. specialize (H4 m). assert (m = S j \/ m <= j)%nat as [H7 | H7] by lia;
         subst; try lra. specialize (H4 ltac:(lia)). lra.
Qed.

Lemma exists_min_of_sequence_on_interval : forall (a : nat -> R) (i j : nat),
  (i <= j)%nat -> exists n : nat, (i <= n <= j)%nat /\ forall m : nat, (i <= m <= j)%nat -> a n <= a m.
Proof.
  intros a i j H1. induction j.
  - assert (i = 0)%nat by lia. subst. exists 0%nat. split; try lia.
    intros m H2. replace m with 0%nat by lia. lra.
  - assert (i = S j \/ i <= j)%nat as [H2 | H2] by lia.
    -- subst. exists (S j). split; try lia. intros m H3. replace m with (S j) by lia. lra.
    -- specialize (IHj H2) as [n [H3 H4]]. assert (a (S j) <= a n \/ a (S j) > a n) as [H5 | H5] by lra.
       + exists (S j). split; try lia. intros m H6. specialize (H4 m). assert (m = S j \/ m <= j)%nat as [H7 | H7] by lia;
         subst; try lra. specialize (H4 ltac:(lia)). lra.
       + exists n. split; try lia. intros m H6. specialize (H4 m). assert (m = S j \/ m <= j)%nat as [H7 | H7] by lia;
         subst; try lra. specialize (H4 ltac:(lia)). lra.
Qed.

Lemma sum_f_ge : forall f i n,
  (i <= n)%nat -> (forall n, f n >= f (S n)) -> sum_f i n f >= INR (n - i + 1) * f n.
Proof.
  intros f i n H1 H2. induction n as [| k IH].
  - replace i with 0%nat by lia. sum_simpl. lra.
  - assert (i = S k \/ i <= k)%nat as [H3 | H3] by lia.
    -- rewrite H3. sum_simpl. solve_INR.
    -- specialize (IH H3). rewrite sum_f_i_Sn_f; try lia. specialize (H2 k).
       assert (INR (k - i + 1) * f k + f (S k) >= INR (S k - i + 1) * f (S k)).
       { solve_INR. apply INR_le in H3. lia. } nra.
Qed.

Lemma sum_f_combine : forall f i n1 n2,
  (i <= n1 < n2)%nat -> sum_f i n2 f = sum_f i n1 f + sum_f (S n1) n2 f.
Proof.
  intros f i n1 n2 H1. induction n2 as [| k IH]; try lia.
  assert (n1 = k \/ n1 < k)%nat as [H2 | H2] by lia.
  - subst. sum_simpl. lra.
  - specialize (IH ltac:(lia)). rewrite sum_f_i_Sn_f; try lia. rewrite IH.
    rewrite sum_f_i_Sn_f; try lia. lra.
Qed.

Lemma sum_n_divisible : forall n : nat,
  Nat.divide 2 (n * (n + 1)).
Proof.
  induction n as [| k IH].
  - exists 0%nat. simpl. reflexivity.
  - replace (S k * (S k + 1))%nat with ((k^2 + k) + (2*k + 2))%nat by (simpl; lia).
    destruct IH as [m H1]. exists (m + (k + 1))%nat. simpl. lia.
Qed.