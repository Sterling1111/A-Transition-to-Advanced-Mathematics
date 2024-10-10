Require Import ZArith Lia Classical List WI_SI_WO.
Import ListNotations.

Open Scope Z_scope.

Theorem quotient_remainder_theorem_existence : forall a d : Z,
  (d >= 1) -> exists q r : Z, a = d * q + r /\ 0 <= r < d.
Proof.
  intros a d Hb.
  set (S z := exists t : Z, z = a - t * d /\ z >= 0).
  assert (Ht : exists t : Z, S t).
  { 
    destruct (Z_le_dec 0 a) as [Ha | Ha].
    - exists a. unfold S. exists 0. split. simpl. rewrite Z.sub_0_r. reflexivity. apply Z.le_ge. apply Ha.
    - unfold not in Ha. exists (a * (1 - d)). unfold S. exists a. split. lia.
      assert (1 - d <= 0) by lia. destruct (Z.eq_dec (1 - d) 0) as [H2 | H2].
      -- lia.
      -- assert (H3 : 1 - d < 0) by lia. assert (H4 : a < 0) by lia. 
         assert (H5 : forall z : Z, z > 0 -> z >= 0) by lia. apply H5. 
         apply Z.lt_gt. apply Z.mul_neg_neg. lia. lia.
  }
  apply well_ordering_Z in Ht.
  - destruct Ht as [r Ht]. destruct Ht as [Ht Ht'].
    unfold S in Ht. destruct Ht as [t Ht]. destruct Ht as [Ht Ht'']. 
    exists t. exists r. split. lia. destruct (classic (r < d)) as [H1 | H1].
    -- lia.
    -- assert (H2 : r >= d) by lia. assert (H3 : a - t * d >= d) by lia.
       assert (H4 : a - d * (t - 1) >= 0) by lia.  assert (H5 : r - d >= 0) by lia.
       assert (H6 : S (r - d)). { unfold S. exists (t + 1). split. lia. lia. }
       assert (H7 : S (a - d * (t + 1))). { unfold S. exists (t + 1). split. lia. lia. }
       assert (H8 : r <= r - d). { apply Ht'. lia. apply H6. } lia.
    - intros z. unfold S. intros H. destruct H as [t H]. lia.
Qed.

Theorem quotient_remainder_theorem_uniqueness : forall a d q1 q2 r1 r2 : Z,
  (d >= 1) /\  a = d * q1 + r1 /\ a = d * q2 + r2 /\ 0 <= r1 < d /\ 0 <= r2 < d
  -> q1 = q2 /\ r1 = r2.
Proof.
  intros a d q1 q2 r1 r2 [H1 [H2 [H3 [H4 H5]]]].
  assert (H: q1 = q2).
  {
    assert (H6 : q1 * d + r1 = q2 * d + r2) by lia.
    assert (H7 : (q1 - q2) * d = r2 - r1) by lia.
    assert (H8 : -d < -r1 <= 0) by lia.
    assert (H9 : 0 <= r2 < d) by lia.
    assert (H10 : -d < r2 - r1 < d) by lia.
    assert (H11 : -d < (q1 - q2) * d < d) by lia.
    destruct H11 as [H11 H12].
    assert (H13 : -1 < q1 - q2).
    { apply Zmult_lt_reg_r with (p := d). lia. lia. }
    assert (H14 : q1 - q2 < 1).
    { apply Zmult_lt_reg_r with (p := d). lia. lia. } 
    lia.
  }
  split.
  - apply H.
  - lia. 
Qed.

Theorem quotient_remainder_theorem : forall a d : Z,
  d >= 1 -> 
  exists! p : (Z * Z), let (q, r) := p in a = d * q + r /\ 0 <= r < d.
Proof.
  intros a d Hd.
  apply unique_existence with (P := fun p : (Z * Z) => let (q, r) := p in a = d * q + r /\ 0 <= r < d).

  split.
  - destruct (quotient_remainder_theorem_existence a d Hd) as [q [r [H1 H2]]].
    exists (q, r). auto.
  
  - intros [q1 r1] [q2 r2] [H1a H1b] [H2a H2b].
    assert (H3 : q1 = q2 /\ r1 = r2) by (apply quotient_remainder_theorem_uniqueness with (a := a) (d := d); auto).
    destruct H3 as [H3a H3b]. rewrite H3a. rewrite H3b. reflexivity.
Qed.

Ltac zforms :=
  match goal with
  | [ |- exists _, ?n = ?num * _ \/ _ ] =>
      destruct (quotient_remainder_theorem_existence n num) as [q [r Hqr]];
      try exists q;
      lia
  | _ => fail "Goal does not match expected pattern"
  end.

Lemma poopyPants : forall n : Z,
  exists k : Z, n = 3 * k \/ n = 3 * k + 1 \/ n = 3 * k + 2.
Proof.
  intros n. zforms. Qed.

Definition ZEven (n : Z) : Prop := exists k : Z, n = 2 * k.
Definition ZOdd (n : Z) : Prop   := exists k : Z, n = 2 * k + 1.

Theorem even_or_odd : forall n : Z,
  ZOdd n \/ ZEven n.
Proof.
  intro n. destruct (quotient_remainder_theorem_existence n 2) as [q [r [H1 H2]]]; try lia.
  destruct (Z.eq_dec r 0) as [H3 | H3].
  - right. unfold ZEven. exists q. lia.
  - left. unfold ZOdd. exists q. lia.
Qed.

Lemma neq_Z : forall a b : Z,
  2 * a = 2 * b + 1 -> False.
Proof.
  intros a b H1. set (a1 := 2 * a + 0). set (a2 := 2 * b + 1).
  pose proof (quotient_remainder_theorem_uniqueness a1 2 a b 0 1) as [H2 H3]; repeat split; try lia.
Qed.