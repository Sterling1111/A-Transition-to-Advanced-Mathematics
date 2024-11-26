Require Import Imports Sets Functions Chapter6 Notations.
Import SetNotations.

Notation subType := SetNotations.subType.

Open Scope R_scope.

Definition n_N (n : nat) : Type := subType (fun x : nat => exists k : nat, (x = n * k)%nat).

Definition eq_cardinality {A B : Type} (X : Ensemble A) (Y : Ensemble B) : Prop :=
  exists f : subType X -> subType Y, bijective f.

Notation "n 'N'" := (n_N n) (at level 0, format "n 'N'").

(* Notation for cardinality equivalence *)
Notation "‖ X ‖ = ‖ Y ‖" := (eq_cardinality (Full_set X) (Full_set Y))
  (at level 80, X at level 0, format "‖ X ‖  =  ‖ Y ‖").

Notation "‖ X ‖ = ‖ Y ‖" := (eq_cardinality (Full_set X) (Full_set Y))
  (at level 80, X at level 0, format "‖ X ‖  =  ‖ Y ‖").

Open Scope Z_scope.

Lemma eq_cardinality_Full_set : forall (A B : Type),
  (exists f : A -> B, bijective f) -> ‖A‖ = ‖B‖.
Proof.
  intros A B [f [H1 H2]]. unfold injective in H1. unfold surjective in H2.
  unfold eq_cardinality.
  exists (fun sa : subType (Full_set A) => mkSubType B (Full_set B) (f (val _ sa)) ltac:(apply Full_intro)).
  split.
  - intros x y H3. destruct x as [x H4], y as [y H5]. simpl in *. specialize (H1 x y).
    specialize (H1 ltac:(inversion H3; reflexivity)). subst. replace H4 with H5.
    2 : { destruct H4, H5. reflexivity. } reflexivity.
  - intros y. destruct y as [y H3]. specialize (H2 y) as [x H4]. exists (mkSubType A (Full_set A) x ltac:(apply Full_intro)).
    simpl. destruct H3, H4. reflexivity.
Qed.

Theorem theorem_29_4 : ‖ ℕ ‖ = ‖ ℤ ‖.
Proof.
  apply eq_cardinality_Full_set.
  set (f := fun n : nat => if Nat.even n then Z.of_nat (n / 2) else - Z.of_nat (n / 2 + 1)).
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
Qed.