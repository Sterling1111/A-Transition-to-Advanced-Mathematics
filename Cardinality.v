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

Definition countably_infinite {T : Type} (A : Ensemble T) : Prop := ‖ ℕ ‖ = ‖ A ‖.
Definition countable {T : Type} (A : Ensemble T) : Prop := Finite_set A \/ countably_infinite A.

Theorem theorem_29_14 : forall (T : Type) (A B : Ensemble T),
  Infinite_set B -> B ⊆ A -> countably_infinite A -> countably_infinite B.
Proof.
  intros T A B H1 H2. unfold countably_infinite. unfold Type_to_Ensemble. intros [[_ H3] | [_ [_ [f [H3 H4]]]]].
  - assert (B <> ⦃⦄) as H5. { apply not_Empty_In. apply Infinite_exists_In; auto. } exfalso. apply H5. autoset.
  - unfold countably_infinite. unfold cardinal_eq. right. repeat split.
    -- apply not_Empty_In. exists 0%nat. apply Full_intro.
    -- apply not_Empty_In. apply Infinite_exists_In; auto.
    -- unfold injective in H3. unfold surjective in H4. 
Admitted.

Definition Q' : Ensemble (ℤ * ℤ) := fun p => let (a, b) := p in b <> 0 /\ Z.gcd a b = 1.
Definition Q'' : Ensemble ℝ := fun r => exists a b : ℤ, b <> 0 /\ Z.gcd a b = 1 /\ (r = (IZR a) / IZR b)%R.
Definition Q''' : Ensemble ℚ := ℚ.

Print find.
Print Pos.of_nat.

Open Scope Q_scope.

Notation "q1 =? q2" := (Qeq_bool q1 q2) (at level 70) : Q_scope.

Definition nat_to_Q (n d : nat) : Q := (Z.of_nat n) # (Pos.of_nat d).
Definition Q_num_nat (q : Q) : nat := Z.to_nat (Qnum q).
Definition Q_den_nat (q : Q) : nat := Pos.to_nat (Qden q).

Fixpoint next_Q (n d : nat) (l : list Q) : (list Q * Q) :=
  let q := nat_to_Q n d in
  match d with
  | 0%nat => (l, 0)
  | 1%nat => (l ++ [q], q)
  | S d' => match (find (fun q' => q' =? q) l) with
            | None => (l ++ [q], q)
            | Some _ => next_Q (n + 1) d' l
            end
  end.

Fixpoint func1 (iter : nat) (n d : nat) (l : list Q) : list Q :=
  match iter with
  | 0%nat => l
  | S iter' =>
      let (l', q) := next_Q n d l in
      let d' := Q_den_nat q in
      let n' := Q_num_nat q in
      match d' with
      | 1%nat => func1 iter' 1 (n' + 1) l'
      | _ => func1 iter' (n' + 1) (d' - 1) l'
      end
  end.

Fixpoint last_element {A : Type} (l : list A) (default : A) : A :=
  match l with
  | [] => default
  | [x] => x
  | _ :: t => last_element t default
  end.

Definition N_Qpos_bijection (n : nat) : Q :=
  let l := func1 (n + 1) 1 1 [1] in
  last_element l 0.

Compute (map N_Qpos_bijection (seq 0 10)).

Theorem theorem_29_5 : ‖ ℕ ‖ = ‖ ℚ ‖.
Proof.
Admitted.