Require Import ZArith Lia Classical List WI_SI_WO FunctionalExtensionality
               Orders Sorting Permutation Chapter18.

Import ListNotations.

Open Scope Z_scope.

Module Znt := ZArith.Znumtheory.

Definition composite (n : Z) : Prop := (1 < n)%Z /\ ~ Znt.prime n.

Definition prime_list (l : list Z) : Prop := Forall Znt.prime l.

Lemma prime_list_fold_right_pos : forall l,
  prime_list l -> fold_right Z.mul 1 l >= 0.
Proof.
  intros l H1. induction l as [| h t IH].
  - simpl. lia.
  - simpl. apply Forall_cons_iff in H1 as [H1 H2]. apply IH in H2. assert (h >= 2) as H3.
    { apply Znt.prime_ge_2 in H1. lia. }
    lia.
Qed.

Lemma in_prime_list : forall l x,
  prime_list l -> In x l -> Znt.prime x.
Proof.
  intros l x H1 H2. unfold prime_list in H1. rewrite Forall_forall in H1. apply H1. auto.
Qed.

Fixpoint max_list_Z (l : list Z) : Z :=
  match (l) with
  | [] => 0
  | x :: xs => Z.max x (max_list_Z xs)
  end.

Lemma in_list_le_max : forall l x,
  In x l -> x <= (max_list_Z l)%Z.
Proof.
  intros l x H. induction l as [| h t IH].
  - inversion H.
  - destruct H as [H | H].
    -- rewrite H. simpl. apply Z.le_max_l.
    -- apply IH in H. simpl. lia.
Qed.

Definition first_n_primes (l : list Z) : Prop :=
  NoDup l /\ prime_list l /\
    (forall x, (Znt.prime x /\ x <= (max_list_Z l)%Z) -> In x l).

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
  - destruct H1 as [H1 _]. apply Z.divide_gcd_iff in H2; lia.
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

Notation In := List.In.

Theorem theorem_19_6 : forall p l,
  Znt.prime p -> (p | fold_right Z.mul 1 l) -> exists x, In x l /\ (p | x).
Proof.
  intros p l H1 H2. assert (p > 1) as H3 by (destruct H1; lia). induction l as [| h t IH]; simpl in *.
  - destruct H2 as [x H2]. pose proof Znt.Zmult_one p x ltac:(lia) ltac:(lia); lia.
  - apply theorem_19_5 in H2 as [H4 | H4]; auto.
    -- exists h. split; auto.
    -- specialize (IH H4) as [x [H5 H6]]. exists x. split; auto.
Qed.

Theorem theorem_19_7 : forall a,
  a > 1 -> (exists p, Znt.prime p /\ (p | a)).
Proof.
  intros a. strong_induction a.
  assert (a = 2 \/ a > 2) as [H2 | H2] by lia.
  - exists 2. split; [apply Znt.prime_2 | exists 1; lia].
  - destruct (Znt.prime_dec a) as [H4 | H4].
    -- exists a. split; [auto | exists 1; lia].
    -- rewrite <- Znt.prime_alt in H4. apply not_and_or in H4 as [H4 | H4]; try lia.
       apply not_all_ex_not in H4 as [p H4]. apply imply_to_and in H4 as [H4 H5]. apply NNPP in H5.
       specialize (IH p ltac:(lia) ltac:(lia)). destruct IH as [p' IH]. exists p'. split; try apply IH.
       apply Z.divide_trans with (m := p); tauto.
Qed.

Lemma fold_right_mul_distributive : forall (k : Z) (l : list Z),
  fold_right Z.mul k l = k * fold_right Z.mul 1 l.
Proof.
  intros k l. induction l as [| h l' IH].
  - simpl. lia.
  - simpl. rewrite IH. lia.
Qed.

Theorem theorem_19_8 : forall a : Z,
  a > 1 -> exists l : list Z,
    prime_list l /\ a = fold_right Z.mul 1 l.
Proof.
    intros a. strong_induction a.
    - assert (a = 2 \/ a > 2) as [H2 | H2] by lia.
      -- exists [2]. split; try (simpl; lia); try (constructor; auto). apply Znt.prime_2.
      -- destruct (Znt.prime_dec a) as [H3 | H3].
         + exists [a]. split; try (simpl; lia); try constructor; auto.
         + rewrite <- Znt.prime_alt in H3. apply not_and_or in H3 as [H3 | H3]; try lia.
           apply not_all_ex_not in H3 as [p H3]. apply imply_to_and in H3 as [H4 H5].
           apply NNPP in H5 as [k H5].
           assert (exists l1 : list Z, prime_list l1 /\ p = fold_right Z.mul 1 l1) as [l1 H11] by (apply IH; lia).
           assert (exists l2 : list Z, prime_list l2 /\ k = fold_right Z.mul 1 l2) as [l2 H12] by (apply IH; nia).
           exists (l1 ++ l2). split; try (apply Forall_app; split; tauto).
           rewrite fold_right_app. rewrite fold_right_mul_distributive. lia.
Qed.

Lemma prime_list_cons : forall l p,
  prime_list (p :: l) -> prime_list l /\ Znt.prime p.
Proof.
  intros l p H1. split.
  - apply Forall_inv_tail in H1. apply H1.
  - apply Forall_inv in H1. apply H1.
Qed.

Lemma prime_list_cons_iff : forall l p,
  prime_list (p :: l) <-> prime_list l /\ Znt.prime p.
Proof.
  intros l p. split.
  - apply prime_list_cons.
  - intros [H1 H2]. apply Forall_cons; auto.
Qed.

Lemma p_div_fold_right_In : forall l p,
  prime_list l -> Znt.prime p -> (p | fold_right Z.mul 1 l) -> In p l.
Proof.
  intros l p H1 H2 H3. induction l as [| h t IH].
  - simpl in H3. apply Znt.prime_ge_2 in H2. destruct H3 as [r1 H3]. assert (r1 = 1) as H4 by lia. lia.
  - simpl in H3. apply prime_list_cons in H1 as [H1 H1']. destruct (Z.eq_dec h p) as [H6 | H6].
    -- rewrite H6. left. reflexivity.
    -- right. apply IH; auto. assert (H7 : ~(p | h)).
       { intros H7. apply Znt.prime_div_prime in H7; auto. } apply theorem_19_5 in H3; try tauto.
       destruct H2 as [H2 _]. lia.
Qed.

Lemma p_notin_ndiv_fold_right : forall l p,
  prime_list l -> Znt.prime p -> ~In p l -> ~(p | fold_right Z.mul 1 l).
Proof.
  intros l p H1 H2 H3 H4. apply p_div_fold_right_In in H4; auto.
Qed.

Lemma divide_factor_l : forall a b c,
  (b | c) -> (a * b | a * c).
Proof.
  intros a b c [k H]. exists k. lia.
Qed.

Lemma count_mul_div_fold_right : forall l z,
  In z l -> (z ^ (Z.of_nat (count_occ Z.eq_dec l z)) | fold_right Z.mul 1 l).
Proof.
  intros l z H1. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct H1 as [H1 | H1].
    -- rewrite H1. destruct (Z.eq_dec z z) as [H2 | H2]; try contradiction. clear H2.
       assert (In z t \/ ~ In z t) as [H2 | H2] by apply classic.
       + replace (Z.of_nat (S (count_occ Z.eq_dec t z))) with (Z.succ (Z.of_nat (count_occ Z.eq_dec t z))) by lia.
         rewrite Z.pow_succ_r. 2 : { lia. } apply divide_factor_l. apply IH; auto.
       + apply (count_occ_not_In Z.eq_dec) in H2. rewrite H2. simpl. exists (fold_right Z.mul 1 t). lia. 
    -- pose proof (Z.eq_dec h z) as [H2 | H2].
       + rewrite H2. destruct (Z.eq_dec z z) as [H3 | H3]; try contradiction. clear H3.
         replace (Z.of_nat (S (count_occ Z.eq_dec t z))) with (Z.succ (Z.of_nat (count_occ Z.eq_dec t z))) by lia.
         rewrite Z.pow_succ_r. 2 : { lia. } apply divide_factor_l. apply IH; auto.
       + destruct (Z.eq_dec h z) as [H3 | H3]; try contradiction. apply IH in H1. destruct H1 as [r H1]. exists (r * h). lia.
Qed.

Lemma z_pow_div_z_div : forall a b c,
  c >= 1 -> (a^c | b) -> (a | b).
Proof.
  intros a b c H1 [k H2]. exists (k * a^(Z.pred c)). rewrite H2.
  - assert (c = 1 \/ c > 1) as [H3 | H3] by lia.
    + rewrite H3. simpl. lia.
    + assert (H4 : exists d, c = Z.succ d) by (exists (Z.pred c); lia). destruct H4 as [d H4]. rewrite H4. rewrite Z.pow_succ_r. 2 : { lia. }
      replace (Z.pred (Z.succ d)) with d by lia. lia.
Qed.

Lemma z_pow_mult : forall a b c,
  a >= 0 -> b >= 0 -> c >= 0 -> a^(b) * a^(c) = a^(b + c).
Proof.
  intros a b c H1 H2 H3. rewrite Z.pow_add_r; lia.
Qed.

Lemma z_mul_div : forall a b c,
  c <> 0 ->
  (c | b) -> a * (b / c) = (a * b) / c.
Proof.
  intros a b c H1 [r1 H2]. rewrite H2. rewrite Z.div_mul; auto. 
  rewrite Z.mul_assoc. rewrite Z.div_mul; auto.
Qed.

Lemma fold_right_div_pow_eq_remove_fold_right : forall l z,
  z <> 0 ->
  fold_right Z.mul 1 l / (z ^ (Z.of_nat (count_occ Z.eq_dec l z))) = fold_right Z.mul 1 (remove Z.eq_dec z l).
Proof.
  intros l z H1. induction l as [| h t IH].
  - simpl. apply Z.div_1_r.
  - assert (In z (h :: t) \/ ~ In z (h :: t)) as [H2 | H2] by apply classic.
    -- simpl. destruct (Z.eq_dec h z) as [H3 | H3].
       + rewrite H3. destruct (Z.eq_dec z z) as [H4 | H4]; try contradiction. clear H4.
         assert (In z t \/ ~ In z t) as [H4 | H4] by apply classic.
         * rewrite <- IH. rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r. 2 : { lia. } pose proof (count_mul_div_fold_right t z H4) as [r H5].
           rewrite H5. rewrite Z.div_mul. 2 : { apply (count_occ_In Z.eq_dec) in H4. apply Z.pow_nonzero. lia. lia. } rewrite Z.mul_comm. rewrite <- Z.mul_assoc.
              replace (z^Z.of_nat (count_occ Z.eq_dec t z) * z) with (z * z^Z.of_nat (count_occ Z.eq_dec t z)) by lia. rewrite Z.div_mul; try lia.
              assert (H6 : z ^ Z.of_nat (count_occ Z.eq_dec t z) <> 0). { apply Z.pow_nonzero; lia. } lia.
         * replace (count_occ Z.eq_dec t z) with (0%nat). 2 : { apply (count_occ_not_In Z.eq_dec) in H4. lia. }
           replace (remove Z.eq_dec z t) with t. 2 : { apply (notin_remove Z.eq_dec) in H4. auto. } rewrite Z.mul_comm. replace (Z.of_nat 1) with 1 by lia.
           rewrite Z.pow_1_r. rewrite Z.div_mul; try lia.
       + destruct (Z.eq_dec z h) as [H4 | H4]; try lia. clear H4. simpl. rewrite <- IH. destruct H2 as [H2 | H2]; try contradiction. pose proof (count_mul_div_fold_right t z H2) as [r H4].
         rewrite H4. rewrite Z.div_mul. 2 : { apply (count_occ_In Z.eq_dec) in H2. apply Z.pow_nonzero. lia. lia. } rewrite Z.mul_comm. rewrite <- Z.mul_assoc.
         replace (z^Z.of_nat (count_occ Z.eq_dec t z) * h) with (h * z^Z.of_nat (count_occ Z.eq_dec t z)) by lia. rewrite Z.mul_assoc. rewrite Z.div_mul; try lia.
         apply (count_occ_In Z.eq_dec) in H2. apply Z.pow_nonzero; lia.
    -- replace (remove Z.eq_dec z (h :: t)) with (h :: t). 2 : { apply (notin_remove Z.eq_dec) in H2. auto. } 
       replace (count_occ Z.eq_dec (h :: t) z) with (0%nat). 2 : { apply (count_occ_not_In Z.eq_dec) in H2. lia. } simpl. rewrite Z.div_1_r. lia.
Qed.

Lemma p_ndiv_fold_right : forall l p,
  prime_list l -> In p l -> ~(p | (fold_right Z.mul 1 l / p ^ (Z.of_nat (count_occ Z.eq_dec l p)))).
Proof.
  intros l p H1 H2. rewrite fold_right_div_pow_eq_remove_fold_right. 
  2 : { apply in_prime_list in H2; auto. apply Znt.prime_ge_2 in H2; lia. }
  intros H3. assert (~In p (remove Z.eq_dec p l)) as H4. { intros H4. apply (in_remove Z.eq_dec) in H4. lia. }
  apply H4. apply p_div_fold_right_In; auto. 2 : { apply in_prime_list in H2; auto. } unfold prime_list in *.
  rewrite Forall_forall in *. intros x H5. apply H1. apply in_remove in H5. tauto.
Qed.

Lemma FTA_unique : forall l1 l2 z p,
  prime_list l1 -> prime_list l2 -> z = fold_right Z.mul 1 l1 -> z = fold_right Z.mul 1 l2 -> 
  count_occ Z.eq_dec l1 p = count_occ Z.eq_dec l2 p.
Proof.
  intros l1 l2 z p H1 H2 H3 H4.
  pose proof (lt_eq_lt_dec (count_occ Z.eq_dec l1 p) (count_occ Z.eq_dec l2 p)) as [[H5 | H5] | H5]; auto.
  - assert (H6 : In p l2). { apply (count_occ_In Z.eq_dec); lia. } pose proof (count_mul_div_fold_right l2 p H6) as H7.
    rewrite <- H4 in H7. assert (count_occ Z.eq_dec l1 p = 0 \/ count_occ Z.eq_dec l1 p > 0)%nat as [H8 | H8] by lia.
    -- assert (H9 : ~In p l1). { intros H9. apply (count_occ_not_In Z.eq_dec) in H9. lia. lia. } 
       assert (H10 : ~(p | fold_right Z.mul 1 l1)). { apply p_notin_ndiv_fold_right; auto. apply in_prime_list in H6; auto. }
       rewrite <- H3 in H10. assert (H11 : (p | z)). { apply z_pow_div_z_div with (c := Z.of_nat (count_occ Z.eq_dec l2 p)); auto; lia. } tauto.
    -- assert (H9 : In p l1). { apply (count_occ_In Z.eq_dec); lia. } pose proof (count_mul_div_fold_right l1 p H9) as H10.
       rewrite <- H3 in H10. assert (H11 : (p | z / p ^ (Z.of_nat (count_occ Z.eq_dec l1 p)))).
       { destruct H7 as [r1 H7]. destruct H10 as [r2 H10]. exists (r1 * p ^ Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p - 1)). rewrite H10. rewrite Z.div_mul. 
         2 : { apply Z.pow_nonzero; try lia. apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6; lia. }
         rewrite <- Z.mul_assoc. rewrite Z.mul_comm with (m := p). rewrite <- Z.pow_succ_r; try lia.
         replace (Z.succ (Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p - 1))) with (Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p)) by lia.
         rewrite Nat2Z.inj_sub; try lia. rewrite Z.pow_sub_r; try lia. 2 : { apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6; lia. }
         assert (H12 : (p ^ Z.of_nat (count_occ Z.eq_dec l1 p) | p ^ Z.of_nat (count_occ Z.eq_dec l2 p))). 
         { exists (p ^ (Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p))). rewrite z_pow_mult; try lia. 
           2 : { apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6; lia. }
           replace (Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p) + Z.of_nat (count_occ Z.eq_dec l1 p)) with (Z.of_nat (count_occ Z.eq_dec l2 p)) by lia. lia. 
         }
         rewrite z_mul_div; auto. 2 : { apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6; lia. }
         rewrite <- H7. rewrite H10. rewrite Z.div_mul; auto. apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6; lia.
       }
       pose proof p_ndiv_fold_right l1 p H1 H9 as H12. rewrite <- H3 in H12. tauto.
  - assert (H6 : In p l1). { apply (count_occ_In Z.eq_dec); lia. } pose proof (count_mul_div_fold_right l1 p H6) as H7.
    rewrite <- H3 in H7. assert (count_occ Z.eq_dec l2 p = 0 \/ count_occ Z.eq_dec l2 p > 0)%nat as [H8 | H8] by lia.
    -- assert (H9 : ~In p l2). { intros H9. apply (count_occ_not_In Z.eq_dec) in H9. lia. lia. } 
       assert (H10 : ~(p | fold_right Z.mul 1 l2)). { apply p_notin_ndiv_fold_right; auto. apply in_prime_list in H6; auto. }
       rewrite <- H4 in H10. assert (H11 : (p | z)). { apply z_pow_div_z_div with (c := Z.of_nat (count_occ Z.eq_dec l1 p)); auto; lia. }
       tauto.
    -- assert (H9 : In p l2). { apply (count_occ_In Z.eq_dec); lia. } pose proof (count_mul_div_fold_right l2 p H9) as H10.
       rewrite <- H4 in H10. assert (H11 : (p | z / p ^ (Z.of_nat (count_occ Z.eq_dec l2 p)))).
       { destruct H7 as [r1 H7]. destruct H10 as [r2 H10]. exists (r1 * p ^ Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p - 1)). rewrite H10. rewrite Z.div_mul.
         2 : { apply Z.pow_nonzero; try lia. apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6; lia. }
         rewrite <- Z.mul_assoc. rewrite Z.mul_comm with (m := p). rewrite <- Z.pow_succ_r; try lia.
         replace (Z.succ (Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p - 1))) with (Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p)) by lia.
         rewrite Nat2Z.inj_sub; try lia. rewrite Z.pow_sub_r; try lia. 2 : { apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6; lia. }
         assert (H12 : (p ^ Z.of_nat (count_occ Z.eq_dec l2 p) | p ^ Z.of_nat (count_occ Z.eq_dec l1 p))). 
         { exists (p ^ (Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p))). rewrite z_pow_mult; try lia. 
           2 : { apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6; lia. }
           replace (Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p) + Z.of_nat (count_occ Z.eq_dec l2 p)) with (Z.of_nat (count_occ Z.eq_dec l1 p)) by lia. lia. 
         }
         rewrite z_mul_div; auto. 2 : { apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6; lia. }
         rewrite <- H7. rewrite H10. rewrite Z.div_mul; auto. apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6; lia.
       }
       pose proof p_ndiv_fold_right l2 p H2 H9 as H12. rewrite <- H4 in H12. tauto.
Qed.

Module ZOrder.
Definition t := Z.
Definition leb := Z.leb.
Lemma leb_total : forall x y : t, leb x y = true \/ leb y x = true.
Proof.
  intros x y; case (Zle_bool_total x y); auto.
Qed.
End ZOrder.

Module ZSort := Sort ZOrder.

Lemma Transitive_Zle_bool : Transitive (fun x y => is_true (x <=? y)%Z).
Proof.
  intros a; unfold is_true; lia.
Qed.

Lemma Sorted_bool_prop : forall l : list Z,
  Sorted Z.le l <-> Sorted ((fun x y => is_true (x <=? y)%Z)) l.
Proof.
  intros l. split.
  - induction l as [| x xs IH].
    -- constructor.
    -- inversion 1; subst. constructor.
      + apply IH. assumption.
      + inversion H3. constructor. unfold is_true. constructor. lia.
  - induction l as [| x xs IH].
    -- constructor. 
    -- inversion 1; subst. constructor.
       + apply IH. assumption.
       + unfold is_true in H3. inversion H3. constructor. constructor. lia.
Qed.

Lemma exists_sorted:  forall (l1 : list Z), exists l2 : list Z, 
  Sorted Z.le l2 /\ Permutation l1 l2.
Proof.
  intros l. exists (ZSort.sort l). rewrite Sorted_bool_prop.
  split;[apply ZSort.Sorted_sort; apply Transitive_Zle_bool | apply ZSort.Permuted_sort].
Qed.

Lemma In_0_fold_right_eq_0_Z : forall l,
  In 0 l -> fold_right Zmult 1 l = 0.
Proof.
  intros l H1. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct H1 as [H1 | H1].
    + rewrite H1. nia.
    + specialize (IH H1). simpl. nia.
Qed.

Lemma fold_right_factor_divides : forall (k : Z) (l : list Z),
  (In k l) -> (k | fold_right Z.mul 1 l).
Proof.
  intros k l H. induction l as [| h l' IH].
  - inversion H.
  - simpl. destruct H as [H | H].
    -- rewrite H. apply Z.divide_factor_l.
    -- apply IH in H. destruct H as [r H]. exists (r * h). lia.
Qed.

Lemma fold_right_Zmult_remove_one_In : forall a l,
  In a l -> (a <> 0) -> fold_right Zmult 1 (remove_one Z.eq_dec a l) = fold_right Zmult 1 l / a.
Proof.
  intros a l H1 H2. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct H1 as [H1 | H1].
    + rewrite H1. destruct (Z.eq_dec a a) as [H3 | H3]; try contradiction. rewrite Z.mul_comm. rewrite Z.div_mul; lia.
    + specialize (IH H1). destruct (Z.eq_dec h a) as [H3 | H3]. rewrite H3. rewrite Z.mul_comm. rewrite Z.div_mul; lia.
      simpl. rewrite IH. pose proof (fold_right_factor_divides a t ltac:(auto)) as [k H4]. rewrite H4. rewrite Z.div_mul; try nia.
      replace (h * (k * a)) with ((h * k) * a) by lia. rewrite Z.div_mul; lia. 
Qed.

Lemma count_occ_eq_prod_right : forall l1 l2,
  (forall n, count_occ Z.eq_dec l1 n = count_occ Z.eq_dec l2 n) -> fold_right Zmult 1 l1 = fold_right Zmult 1 l2.
Proof.
  intros l1 l2 H1. generalize dependent l2. induction l1 as [| h t IH].
  - intros l2 H1. simpl in *. assert (H2 : forall n, count_occ Z.eq_dec l2 n = 0%nat) by (intros n; specialize (H1 n); lia). 
    apply count_occ_inv_nil in H2. rewrite H2. reflexivity.
  - intros l2 H1. simpl. specialize (IH (remove_one Z.eq_dec h l2)). rewrite IH.
    2 : { 
      intros z. assert (In z l2 \/ ~In z l2) as [H3 | H3] by apply classic.
      - assert (h = z \/ h <> z) as [H4 | H4] by apply classic.
        -- rewrite H4 in *. specialize (H1 z). rewrite count_occ_cons_eq in H1; auto. rewrite remove_one_In; auto. lia.
        -- specialize (H1 z). rewrite count_occ_cons_neq in H1; auto. rewrite count_occ_remove_one_not_eq; auto.
      - assert (h = z \/ h <> z) as [H4 | H4] by apply classic.
        -- rewrite H4 in *. specialize (H1 z). apply (count_occ_not_In Z.eq_dec) in H3. rewrite H3 in H1. rewrite count_occ_cons_eq in H1; auto. lia.
        -- specialize (H1 z). rewrite count_occ_cons_neq in H1; auto. rewrite count_occ_remove_one_not_eq; auto.
    }
    specialize (H1 h). rewrite count_occ_cons_eq in H1; auto. assert (In h l2) as H3.
    { rewrite (count_occ_In Z.eq_dec). lia. } assert (h = 0 \/ h <> 0) as [H4 | H4] by nia. rewrite H4. rewrite In_0_fold_right_eq_0_Z with (l := l2); try lia. rewrite <- H4. auto.
     rewrite fold_right_Zmult_remove_one_In; auto. pose proof fold_right_factor_divides h l2 ltac:(auto) as [k H5]. rewrite H5. rewrite Z.div_mul; lia.
Qed.

Lemma fold_right_Rmult_Permutation : forall l1 l2,
  Permutation l1 l2 -> fold_right Z.mul 1 l1 = fold_right Z.mul 1 l2.
Proof.
  intros l1 l2 H1. rewrite (Permutation_count_occ Z.eq_dec) in H1. apply count_occ_eq_prod_right; auto.
Qed.

Lemma HdRel_trans : forall l x y,
  HdRel Z.le y l -> x <= y -> HdRel Z.le x l.
Proof.
  intros l x y H1 H2. induction l as [| h t IH].
  - apply HdRel_nil.
  - apply HdRel_cons. apply HdRel_inv in H1. lia.
Qed.

Lemma Sorted_cons_In : forall l x y,
  Sorted Z.le (x :: l) -> In y l -> x <= y.
Proof.
  intros l x y H1 H2. induction l as [| h t IH].
  - inversion H2.
  - apply Sorted_inv in H1 as [H1 H3]. apply HdRel_inv in H3; auto. inversion H2 as [H4 | H4]; try nia. apply IH; auto.
    apply Sorted_cons; repeat apply Sorted_inv in H1 as [H5 H6]; auto. apply HdRel_trans with (y := h); auto.
Qed.

Lemma Sorted_Permutation_equal : forall l1 l2,
  Permutation l1 l2 -> Sorted Z.le l1 -> Sorted Z.le l2 -> l1 = l2.
Proof.
  intros l1 l2 H1 H2 H3. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2 H1 H3. apply Permutation_nil in H1. rewrite H1. reflexivity.
  - intros l2 H3 H4. destruct l2 as [| h2 t2].
    -- apply Permutation_sym in H3. apply Permutation_nil in H3. auto.
    -- apply Sorted_inv in H2 as [H2 H5]. specialize (IH H2 t2). assert (In h1 (h1 :: t1) -> In h1 (h2 :: t2)) as H6.
       { apply Permutation_in; auto. } assert (In h2 (h2 :: t2) -> In h2 (h1 :: t1)) as H7.
       { apply Permutation_in. apply Permutation_sym; auto. } assert (In h1 (h2 :: t2)) as H8 by (apply H6; left; reflexivity).
       assert (In h2 (h1 :: t1)) as H9 by (apply H7; left; reflexivity). assert (h1 = h2) as H10.
       {
        destruct H8 as [H8 | H8]; destruct H9 as [H9 | H9]; try lia; try inversion H8; try inversion H9. pose proof (Z.lt_trichotomy h1 h2) as [H10 | [H10 | H10]]; try nia.
        - assert (h2 <= h1) as H11. { apply Sorted_cons_In with (x := h2) (l := t2); auto. } lia.
        - assert (h1 <= h2) as H11. { apply Sorted_cons_In with (x := h1) (l := t1); auto. } lia.
       }
       
      rewrite H10. apply f_equal. apply IH.
      rewrite <- H10 in H3. apply Permutation_cons_inv in H3; auto. apply Sorted_inv in H4 as [H4 H11]; auto.
Qed.

Theorem theorem_19_9 : forall n,
  n > 1 -> exists! l, prime_list l /\ Sorted Z.le l /\ n = fold_right Z.mul 1 l.
Proof.
  intros n H1. pose proof theorem_19_8 n H1 as [l [H2 H3]]. pose proof exists_sorted l as [l2 [H4 H5]].
  exists l2; repeat split; auto.
  - unfold prime_list in *. rewrite Forall_forall in *. intros x H6. apply H2. apply Permutation_sym in H5.
    apply (Permutation_in x) in H5; auto.
  - pose proof theorem_19_8 n ltac:(lia) as [l3 [H6 H7]]. apply fold_right_Rmult_Permutation in H5. lia.
  - intros l3 [H6 [H7 H8]]. apply Sorted_Permutation_equal; auto. rewrite (Permutation_count_occ Z.eq_dec). intros x.
    apply FTA_unique with (z := n); auto. 2 : { rewrite H3. apply fold_right_Rmult_Permutation; auto. }
    apply Forall_forall; intros y H9. apply Permutation_sym in H5. apply (Permutation_in y) in H5; auto.
    unfold prime_list in H2. rewrite Forall_forall in H2. apply H2; auto.
Qed.

Lemma prime_list_product_gt_1 : forall l,
  prime_list l -> fold_right Z.mul 1 l >= 1.
Proof.
  intros l H1. induction l as [| h t IH].
  - simpl. lia.
  - simpl. unfold prime_list in *. apply Forall_cons_iff in H1 as [H1 H2]. apply IH in H2.
    assert (h >= 2) as H3. { apply Znt.prime_ge_2 in H1. lia. }
    lia.
Qed.

Lemma prime_no_div : forall p z,
  Znt.prime p -> (p | z) -> ~(p | z + 1).
Proof.
  intros p z H1 H2 H3. destruct H2 as [r H2]. destruct H3 as [s H3].
  assert (p | 1) as H4 by (exists (s - r); lia). assert (p >= 2) as H5.
  { apply Znt.prime_ge_2 in H1. lia. }
  assert (p = 1) as H6. { destruct H4 as [t H4]. assert (t > 0) by lia. nia. }
  lia.
Qed.

Theorem theorem_19_14_a : forall (l : list Z),
  first_n_primes l -> exists p : Z, Znt.prime p /\ p > max_list_Z l.
Proof.
  intros l [H1 [H2 H3]]. set (N := fold_right Z.mul 1 l + 1).
  assert (N > 1) as H4 by (destruct l; apply prime_list_product_gt_1 in H2; lia).
  destruct (theorem_19_7 N H4) as [q [H5 H6]]. exists q. split; auto.
  destruct (in_dec Z.eq_dec q l) as [H7 | H7].
  - assert ((q | fold_right Z.mul 1 l)) as H8 by (apply fold_right_factor_divides; auto).
    unfold N in H6. pose proof (prime_no_div q (fold_right Z.mul 1 l) H5 H8 H6) as H9. lia.
  - specialize (H3 q). tauto. 
Qed.

Lemma gt_list_max_not_in : forall l x,
  (x > max_list_Z l)%Z -> ~(In x l).
Proof.
  intros l x H1 H2. induction l as [| h t IH].
  - inversion H2.
  - simpl in H1. simpl in H2. destruct H2 as [H2 | H2].
    -- rewrite H2 in H1. lia.
    -- apply IH in H2. lia. lia.
Qed.

Lemma le_max_list_Z : forall l x z,
  x <= max_list_Z (z :: l) -> x = z \/ (x < z /\ x > max_list_Z l) \/ x <= max_list_Z l.
Proof.
  intros l x z H1. induction l as [| h l' IH].
  - simpl in *. assert (H2 : z <= 0 \/ z > 0) by lia. destruct H2.
    -- lia.
    -- lia.
  - simpl in *. assert (H2 : z <= h \/ z > h) by lia. destruct H2.
    -- simpl in H1. lia.
    -- simpl in H1. lia.
Qed.

Lemma prime_list_len : forall n,
  exists l, first_n_primes l /\ length l = n.
Proof.
  intros n. induction n as [| k IH].
  - exists []. split.
    -- repeat split; repeat constructor. intros x [H1 H2]. simpl in H2.
       assert (H3 : x >= 2) by (apply Znt.prime_ge_2 in H1; lia). lia.
    -- simpl. reflexivity.
  - destruct IH as [l [H1 H2]]. destruct (theorem_19_14_a l H1) as [p [H3 H4]].
    set (E := (fun x => (Znt.prime x /\ x > max_list_Z l)%Z)).
    assert (exists p, E p) as [p' H5]. { exists p. unfold E. split; auto. }
    assert (H6 : forall z, E z -> z >= 0).
    { intros z [H6 H7]. assert (z >= 2). { apply Znt.prime_ge_2 in H6. lia. } lia. }
    assert (H7 : exists z, E z). { exists p'. apply H5. }
    pose proof (well_ordering_Z E H6 H7) as [z [[H8 H9] H10]].
    exists (z :: l). split.
    -- repeat split.
      + constructor. apply gt_list_max_not_in. lia. unfold first_n_primes in H1. tauto.
      + unfold prime_list. unfold first_n_primes in H1; apply Forall_cons; tauto.
      + intros x [H11 H12]. simpl. apply le_max_list_Z in H12 as [H12 | [H12 | H12]].
        * lia.
        * destruct H12 as [H12 H13]. specialize (H10 x). assert (x >= 0) as H14.
          { apply Znt.prime_ge_2 in H11. lia. }
          assert (E x) as H15. { unfold E. split. apply H11. apply H13. }
          apply H10 in H15. 2 : { apply H14. } lia.
        * right. apply H1. split. apply H11. apply H12.
    -- simpl. lia.
Qed.

Lemma list_len_cons : forall h (l : list Z),
  length (h :: l) = S (length l).
Proof.
  intros h l. simpl. reflexivity.
Qed.

Lemma max_list_cons_ge : forall l h m,
  m >= max_list_Z (h :: l) -> m >= h /\ m >= max_list_Z l.
Proof.
  intros l h m H. induction l as [| h' l' IH].
  - simpl in *. lia.
  - simpl in *. assert (m >= h /\ m >= max_list_Z l') as [H1 H2] by lia. split.
    -- lia.
    -- lia.
Qed.

Lemma max_list_ge_not_in : forall l h,
  h > 0 -> h >= max_list_Z l /\ ~ In h l -> h > max_list_Z l.
Proof.
  intros l h H1 [H2 H3]. induction l as [| h' l' IH].
  - simpl. lia.
  - simpl. assert (~ In h l') as H4. { pose proof in_cons h' h l' as H4. tauto. }
    assert (h >= max_list_Z l') as H5. { apply max_list_cons_ge in H2 as [H2 H6]. apply IH in H4 as H7. lia. lia. }
    assert (H6 : h > max_list_Z l'). { apply IH in H4 as H6. lia. lia. }
    assert (H7 : h <> h'). { intros H7. rewrite H7 in H3. assert (In h' (h' :: l')) as H8 by apply in_eq. tauto. }
    pose proof (max_list_cons_ge l' h' h) as [H8 H9]. lia. lia.
Qed.

Lemma max_list_ge_not_in' : forall l h,
  max_list_Z l > 0 -> max_list_Z l >= h /\ ~ In h l -> max_list_Z l > h.
Proof.
  intros l h H1 [H2 H3]. induction l as [| h' l' IH].
  - simpl in *. lia.
  - simpl. assert (~ In h l') as H4. { pose proof in_cons h' h l' as H4. tauto. }
    assert (max_list_Z (h' :: l') = h' \/ max_list_Z (h' :: l') = max_list_Z l') as [H5 | H5] by (simpl; lia).
    -- rewrite H5 in H2. assert (h' <> h) as H6.
       { intros H6. rewrite H6 in H3. assert (In h' (h' :: l')) as H7 by apply in_eq. rewrite H6 in H7. tauto. } lia.
    -- assert (max_list_Z l' >= h) as H6. { rewrite H5 in H2. tauto. }
       assert (max_list_Z l' > h) as H7. { apply IH in H4 as H7; lia; auto. }
       lia.
Qed.

Definition Zseq_pos (seq : list nat) : list Z :=
  map Z.of_nat (seq).

Lemma in_Zseq_pos : forall start len x,
  let l := seq start len in
    x > 0 -> In (Z.to_nat x) (seq start len) -> In x (Zseq_pos l).
Proof.
  intros start len x l H. unfold Zseq_pos.
  rewrite in_map_iff. exists (Z.to_nat x). split. lia. auto.
Qed.

Lemma Zseq_len : forall start len,
  let l := seq start len in
    length (l) = length (Zseq_pos l).
Proof.
  intros start len. unfold Zseq_pos. rewrite map_length. reflexivity.
Qed.

Lemma list_has_len : forall (l : list Z) (a : Z),
  In a l -> (length l > 0)%nat.
Proof.
  intros l a. induction l as [| h l' IH].
  - simpl. lia.
  - simpl. intros [H1 | H1]; lia.
Qed.

Lemma remove_one_remains : forall l x1 x2,
  In x1 l -> x1 <> x2 -> In x1 (remove_one Z.eq_dec x2 l).
Proof.
  intros l x1 x2 H. induction l as [| h l' IH].
  - inversion H.
  - simpl. intros H1. destruct (Z.eq_dec h x2) as [H2 | H2].
    -- simpl in H. destruct H as [H | H].
       --- lia.
       --- tauto.
    -- simpl. simpl in H. tauto.
Qed.

Lemma in_notin_neq : forall (l : list Z) x1 x2,
  In x1 l -> ~ (In x2 l) -> x1 <> x2.
Proof.
  intros l x1 x2 H1 H2. induction l as [| h l' IH].
  - inversion H1.
  - simpl in *. destruct H1 as [H1 | H1].
    -- rewrite H1 in H2. tauto.
    -- tauto.
Qed.

Lemma remove_one_len : forall l x,
  In x l -> length (remove_one Z.eq_dec x l) = (length l - 1)%nat.
Proof.
  intros l x H. induction l as [| h l' IH].
  - inversion H.
  - simpl. destruct (Z.eq_dec h x) as [H1 | H1].
    -- lia.
    -- simpl. destruct H as [H | H]. lia. rewrite IH.
       --- assert (length l' > 0)%nat as H2. { apply list_has_len with (a := x). apply H. } lia.
       --- apply H.
Qed.

Theorem longer_list:
    forall l1 l2 : list Z,
    (forall x : Z, In x l1 -> In x l2) ->
    (exists x : Z, In x l2 /\ ~ In x l1) ->
    NoDup l1 ->
    (length l2 > length l1)%nat.
  Proof.
    intros l1 l2 H1 H2 H3. generalize dependent l2.
    induction l1 as [| h l1' IH].
    - intros l2 H4 H5. simpl in *. destruct H5 as [x H5]. assert (exists a, In a l2) as [a H6].
    { exists x. apply H5. } apply list_has_len in H6. lia.
    - intros l2 H4 [a [H5 H6]]. apply NoDup_cons_iff in H3. destruct H3 as [H3 H3'].
      specialize (IH H3' (remove_one Z.eq_dec a l2)). apply not_in_cons in H6 as [H6 H6'].
      assert (In h (remove_one Z.eq_dec a l2)) as H7.
      { apply remove_one_remains. apply (H4 h). simpl. lia. lia. }
      assert (length (remove_one Z.eq_dec a l2) > length l1')%nat as H8.
      { apply IH. intros x H8. apply remove_one_remains. apply (H4 x). simpl. tauto. 2 : { exists h. tauto. }  apply in_notin_neq with (l := l1') (x2 := a). apply H8. apply H6'. }
      rewrite remove_one_len in H8. simpl. lia. tauto.
  Qed.

Theorem pigeonhole_principle_Z : forall (l1 l2 : list Z),
  (forall x, In x l1 -> In x l2) -> (length l2 < length l1)%nat ->
    ~ NoDup l1.
Proof.
  intros l1. induction l1 as [|a l1' IH].
  - simpl. lia.
  - simpl. intros l2 H1 H2. destruct (in_dec Z.eq_dec a (l1')) as [H3 | H3].
    -- intros H4. apply NoDup_cons_iff in H4 as [H4 H5]. tauto.
    -- intros H4. apply IH with (l2 := l2).
       3 : { apply NoDup_cons_iff in H4. tauto. }
       intros x H5. specialize (H1 x). assert (a = x \/ In x l1') as H6 by tauto. tauto.
       assert (H5 : (length l2 > length l1')%nat).
       { apply longer_list. intros x H5. apply (H1 x). tauto. exists a. split. apply (H1 a).
        tauto. tauto. apply NoDup_cons_iff in H4. tauto. }
       lia.
Qed.

Lemma in_list_1 : forall l,
  Z.of_nat (length l) > 0 -> NoDup l -> Forall (fun x => x > 0) l -> Z.of_nat (length l) = max_list_Z l -> In 1 l.
Proof.
  intros l H1 H2 H3 H4. destruct (in_dec Z.eq_dec 1 l) as [H5 | H5]. apply H5.
  set (l2 := Zseq_pos (seq 2 (Z.to_nat (max_list_Z l - 1)))). assert (~NoDup l) as H6.
  - apply pigeonhole_principle_Z with (l2 := l2).
    2 : { assert (length l2 = Z.to_nat (max_list_Z l) - 1)%nat. { unfold l2. rewrite <- Zseq_len. rewrite seq_length. lia. } lia. }
    intros x H6. apply in_Zseq_pos. rewrite Forall_forall in H3. specialize (H3 x). tauto. apply in_seq.
    replace (2 + Z.to_nat (max_list_Z l - 1))%nat with (Z.to_nat (max_list_Z l) + 1)%nat by lia. pose proof H6 as H6'. pose proof H6 as H6''.
    apply in_list_le_max in H6. rewrite Forall_forall in H3. specialize (H3 x). apply H3 in H6'. assert (~x = 1). unfold not in *. intros H7. apply H5. rewrite H7 in H6''. tauto.
    lia.
  - tauto.
Qed.

Lemma list_len_lt_max : forall l,
  Forall (fun x => x > 1) l /\ NoDup l -> Z.of_nat (length l) <= max_list_Z l.
Proof.
  intros l. induction l as [| h l' IH].
  - intros [H1 H2]. simpl. lia.
  - intros [H1 H2]. apply Forall_cons_iff in H1 as [H1 H1']. apply NoDup_cons_iff in H2 as [H2 H3].
    assert (Z.of_nat(length l') <= max_list_Z l') as H4 by (apply IH; split; auto).
    rewrite list_len_cons. assert (max_list_Z (h :: l') = h \/ max_list_Z (h :: l') = max_list_Z l') as [H5 | H5] by (simpl; lia).
    -- rewrite H5. assert (H6 : h >= max_list_Z l') by (induction l'; simpl in *; lia).
       pose proof (max_list_ge_not_in l' h) as H7. assert (H8 : h > 0) by lia. apply H7 in H8. lia. auto.
    -- rewrite H5. assert (H6 : max_list_Z l' >= h) by (induction l'; simpl in *; lia).
       pose proof (max_list_ge_not_in' l' h) as H7. assert (H8 : max_list_Z l' > 0) by lia. apply H7 in H8. 2 : { tauto. }
       assert (Z.of_nat (length l') = max_list_Z l' \/ Z.of_nat (length l') < max_list_Z l') as [H9 | H9].
       --- lia.
       --- rewrite <- H5 in H9. assert (NoDup (h :: l')) as H10 by (apply NoDup_cons; auto).
           assert (Z.of_nat (length l') = max_list_Z l' \/ Z.of_nat (length l') < max_list_Z l') as [H11 | H11] by lia.
           2 : { lia. } apply in_list_1 in H11.
           + rewrite Forall_forall in H1'. specialize (H1' 1). apply H1' in H11. lia.
           + lia.
           + apply H3.
           + assert (H12 : Forall (fun x : Z => x > 1) l' -> Forall (fun x : Z => x > 0) l').
             { intros H12. rewrite Forall_forall in H12. rewrite Forall_forall. intros x H13. apply H12 in H13. lia. }
             tauto.
      --- lia.
Qed.

Lemma max_primes_ge_len : forall l,
  first_n_primes l -> max_list_Z l >= Z.of_nat (length l).
Proof.
  intros l H1. pose proof Znt.prime_ge_2 as H2.
  pose proof (Znt.not_prime_1) as H3. assert (H4 : ~ In 1 l).
  { intros H4. unfold first_n_primes in H1. destruct H1 as [H1 [H5 H6]]. unfold prime_list in H5.
    rewrite Forall_forall in H5. specialize (H5 1). apply H5 in H4. tauto. }
  unfold first_n_primes in H1. destruct H1 as [H1 [H5 H6]]. unfold prime_list in H5. rewrite Forall_forall in H5.
  apply Z.le_ge. apply list_len_lt_max. split. rewrite Forall_forall. intros x H7. specialize (H5 x). apply H5 in H7.
  apply Znt.prime_ge_2 in H7. lia. apply H1.
Qed.

Lemma prime_in_first_n_primes : forall p,
  Znt.prime p -> exists l, first_n_primes l /\ In p l.
Proof.
  intros p H1. pose proof (prime_list_len (Z.to_nat p)) as [l [H2 H3]].
  exists l. split.
  - apply H2.
  - apply H2. apply max_primes_ge_len in H2. rewrite H3 in H2. rewrite Z2Nat.id in H2.
    2 : { apply Znt.prime_ge_2 in H1. lia. }
    split. apply H1. lia.
Qed.

Lemma gt_max_gt_all : forall (l : list Z) x1 x2,
  In x1 l -> x2 > max_list_Z l -> x2 > x1.
Proof.
  intros l x1 x2 H1 H2. induction l as [| h l' IH].
  - inversion H1.
  - simpl in H1. simpl in H2. destruct H1 as [H1 | H1].
    -- lia.
    -- apply IH. apply H1. lia.
Qed.

Theorem theorem_19_14_b : forall p1,
  Znt.prime p1 -> exists p2, Znt.prime p2 /\ p2 > p1.
Proof.
  intros p1 H1.
  apply prime_in_first_n_primes in H1 as [l [H1 H2]].
  pose proof (theorem_19_14_a l H1) as [p2 [H3 H4]]. exists p2. split.
  - apply H3.
  - apply gt_max_gt_all with (l := l); tauto.
Qed.