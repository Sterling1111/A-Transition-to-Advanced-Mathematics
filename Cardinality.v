Require Import Imports Sets Functions Chapter6 Notations.
Import SetNotations.

Notation subType := SetNotations.subType.

Open Scope R_scope.

Definition n_N (n : nat) : Type := subType (fun x : nat => exists k : nat, (x = n * k)%nat).

Notation "n 'N'" := (n_N n) (at level 0, format "n 'N'").

Open Scope Z_scope.

Theorem theorem_29_4 : ‖ ℕ ‖ = ‖ ℤ ‖.
Proof.
  apply eq_cardinality_Type.
  set (f := fun n : nat => if Nat.even n then Z.of_nat (n / 2) else - Z.of_nat (n / 2 + 1)). left. split.
  exists f. split.
  - intros x y H1. unfold f in H1. destruct (Nat.even x) eqn:H2, (Nat.even y) eqn:H3.
    -- apply Nat.even_spec in H2 as [j H2], H3 as [k H3]; subst. apply Nat2Z.inj in H1.
       do 2 (rewrite Nat.mul_comm, Nat.div_mul in H1; try lia).
    -- pose proof Zle_0_nat (x / 2) as H4. pose proof Zle_0_nat (y / 2 + 1) as H5. lia.
    -- pose proof Zle_0_nat (x / 2 + 1) as H4. pose proof Zle_0_nat (y / 2) as H5. lia.
    -- apply Z.opp_inj in H1. apply Nat_even_false_Odd in H2 as [j H2], H3 as [k H3]; subst.
       apply Nat2Z.inj in H1. rewrite Nat.mul_comm in H1. rewrite Nat.mul_comm with (n := 2%nat) in H1.
       rewrite Nat.div_add_l in H1; try lia. rewrite Nat.div_add_l in H1; try lia.
  - intros y. assert (y >= 0 \/ y < 0) as [H1 | H1] by lia.
    -- exists (2 * Z.to_nat y)%nat. unfold f. destruct (Nat.even (2 * Z.to_nat y)) eqn:H2.
       * rewrite Nat.mul_comm. rewrite Nat.div_mul; try lia.
       * apply Nat_even_false_Odd in H2 as [j H2]. lia.
    -- exists (2 * Z.to_nat (- y) - 1)%nat. unfold f. destruct (Nat.even (2 * Z.to_nat (- y) + 1)) eqn:H2.
       * apply Nat.even_spec in H2 as [j H2]. lia.
       * destruct (Nat.even (2 * Z.to_nat (- y) - 1)) eqn:H3.
         + apply Nat.even_spec in H3 as [j H3]. lia.
         + apply Nat_even_false_Odd in H3 as [j H3]. rewrite H3. rewrite Nat.mul_comm.
           rewrite Nat.div_add_l; try lia. simpl. lia.
  - exists 0%nat, 0%Z. auto.
Qed.

Lemma cardinal_eq_refl : forall (T : Type) (A : Ensemble T), ‖ A ‖ = ‖ A ‖.
Proof.
  intros T A. pose proof classic (A = ⦃⦄) as [H1 | H1]; [left | right; repeat split]; auto.
  - exists (fun x => x). split.
    -- intros x y H2. auto.
    -- intros y. exists y. auto.
Qed.

Lemma cardinal_eq_sym : forall (T1 T2 : Type) (A : Ensemble T1) (B : Ensemble T2), ‖ A ‖ = ‖ B ‖ -> ‖ B ‖ = ‖ A ‖.
Proof.
  intros T1 T2 A B [[H1 H2] | [H1 [H2 [f [H3 H4]]]]]; [left | right; repeat split]; auto.
  apply choice in H4 as [g H5]. exists g. split.
  - intros x y H6. specialize (H5 (f (g x))) as H7. rewrite H6 in H7 at 2.
    do 3 rewrite H5 in H7; auto.
  - intros y. specialize (H3 y (g (f y))). specialize (H5 (f y)) as H6.
    rewrite <- H6 in H3 at 1. exists (f y). rewrite H3; auto. rewrite H6. auto.
Qed.

Definition countably_infinite {T : Type} (A : Ensemble T) : Prop := ‖ A ‖ = ‖ ℕ ‖.
Definition countable {T : Type} (A : Ensemble T) : Prop := Finite_set A \/ countably_infinite A.

Theorem theorem_29_14 : forall (T : Type) (A B : Ensemble T),
  ~Finite_set B -> B ⊆ A -> countably_infinite A -> countably_infinite B.
Proof.
  intros T A B H1 H2 [[_ H3] | [_ [_ [f [H3 H4]]]]].
  - exfalso. apply (not_Empty_In ℕ ℕ); auto. exists 0%nat. constructor.
  - unfold countably_infinite. (* apply cardinal_eq_sym *) unfold cardinal_eq. right. repeat split.
    -- admit.
    -- admit.
    -- assert (H5 : forall x : subType B, val B x ∈ A) by (destruct x; autoset).
       set (b_to_a := fun x : subType B => mkSubType T A (val B x) ltac:(apply (H5 x))).
       set (g := fun x : subType B => f (b_to_a x)). exists g. split.
       + intros x y H6. unfold injective in H3. destruct x, y. unfold g in H6. apply H3 in H6.
         unfold b_to_a in H6. simpl in H6. inversion H6. subst. replace property0 with property1.
         2 : { apply proof_irrelevance. } reflexivity.
       + admit.
Admitted.

Theorem theorem_29_5 : ‖ ℕ ‖ = ‖ ℚ ‖.
Proof.
Admitted.