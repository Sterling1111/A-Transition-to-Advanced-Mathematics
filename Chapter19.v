Require Import ZArith Lia Classical Reals Lra Classical_sets List
               Ensembles QArith ClassicalFacts Finite_sets Powerset Finite_sets_facts Image 
               NArith DecimalString DecimalNat DecimalNat Decimal
               Fibonacci Sums Sets Binomial QRT WI_SI_WO Prime.

Require Export Chapter18.

Import ListNotations SetNotations Choose_Notations.

Open Scope Z_scope.

Section section19_1.
  Import String.

  Fixpoint element_divides (z : Z) (l : list Z) : bool := 
  match l with 
  | [] => false
  | h :: t => if Z.eqb (Z.rem z h) 0 then true else element_divides z t
  end.

  Lemma Z_rem_0 : forall z : Z, Z.rem z 0 = z.
  Proof.
    intros z.
    unfold Z.rem, Z.quotrem. destruct z; reflexivity.
  Qed.

  Lemma element_divides_correct : forall z l, element_divides z l = true -> exists x, In x l /\ (x | z).
  Proof.
    intros z l H1. induction l as [| h t IH].
    - inversion H1.
    - simpl in H1. destruct (Z.rem z h =? 0) eqn:Heq.
      -- assert (h = 0 \/ h <> 0) as [H2 | H2]; assert (z = 0 \/ z <> 0) as [H3 | H3]; try lia; subst.
        * exists 0. split. left. reflexivity. apply Z.divide_0_r.
        * assert (Z.rem z 0 = z) as H4 by apply Z_rem_0. lia.
        * exists h. split. left. reflexivity. exists 0; lia.
        * exists h. split. left. reflexivity. apply Z.rem_divide; lia.
      -- apply IH in H1. destruct H1 as [x [H4 H5]]. exists x. split; [right | auto]; auto.
  Qed.

  Definition is_prime (z : Z) (first_primes : list Z) : list Z := 
    if z <? 2 then [] else
    if z =? 2 then [2] else
    if (element_divides z first_primes) then first_primes else z :: first_primes.

  Definition find_primes_le (n : nat) : list Z := 
    List.rev (fold_left (fun l z => is_prime z l) (Zseq_pos (seq 2 (n-1))) []).

  Fixpoint count_divisors (n p : Z) (count : nat) {struct count} : nat :=
    match count with
    | O => 0
    | S count' =>
      if (n mod p =? 0)%Z then S (count_divisors (n / p) p count')
      else 0
    end.

  Definition canonical_prime_factorization_list (n : nat) : list (Z * Z) := 
    let l := find_primes_le n in
    let l' := filter (fun x => Z.rem (Z.of_nat n) x =? 0) l in
    map (fun p => (p, Z.of_nat (count_divisors (Z.of_nat n) p (n)))) l'.

  Open Scope string_scope.

  Definition canonical_prime_factorization_string (n : nat) : string := 
    let l := canonical_prime_factorization_list n in
    let s := Z_to_string (Z.of_nat n) ++ " = " ++ fold_left (fun s p => s ++ Z_to_string (fst p) ++ "^" ++ Z_to_string (snd p) ++ "*") l "" in
    String.substring 0 (String.length s - 1) s.

  Close Scope string_scope.

  (*
  Compute canonical_prime_factorization_string 27.
  Compute canonical_prime_factorization_string 3072.
  Compute canonical_prime_factorization_string 60.
  *)  
End section19_1.


Lemma lemma_19_2 : forall p l,
  Znt.prime p -> (p | fold_right Z.mul 1 l) -> exists x, In x l /\ (p | x).
Proof.
  apply theorem_19_6.
Qed.

Open Scope list_scope.

Lemma lemma_19_3 : forall n,
  n > 1 -> exists p, Znt.prime p /\ (p | n) /\ forall d, (d | n) -> d > 1 -> p <= d.
Proof.
  intros n H1. pose proof (theorem_19_9 n H1) as [l [[H2 [H3 H4]] H5]]. assert (length l = 0 \/ length l > 0)%nat as [H6 | H6] by lia.
  - rewrite length_zero_iff_nil in H6. subst. simpl in H1. lia.
  - exists (nth 0 l 0); split; [ | split].
    -- unfold prime_list in H2. rewrite Forall_forall in H2. assert (In (nth 0 l 0) l) as H7. { apply nth_In. lia. }
       specialize (H2 _ H7); apply H2.
    -- rewrite H4. destruct l; [simpl in *; lia | simpl; apply Z.divide_factor_l].
    -- intros d H7 H8. assert (nth 0 l 0 <= d \/ nth 0 l 0 > d) as [H9 | H9]; try lia.
       pose proof theorem_19_7 _ H8 as [p [H10 H11]]. pose proof Z.divide_trans _ _ _ H11 H7 as H12.
       rewrite H4 in H12. pose proof lemma_19_2 _ _ H10 H12 as [x [H13 H14]]. unfold prime_list in H2. 
       rewrite Forall_forall in H2. specialize (H2 _ H13). apply Znt.prime_alt in H2 as [H2_pos H2].
       assert (nth 0 l 0 <= x) as H15.
       {
          destruct l. simpl in *; lia. assert (x = z \/ x <> z) as [H15 | H15] by lia. simpl. lia.
          destruct H13 as [H13 | H13]; try lia. pose proof (Sorted_cons_In l _ _ H3 H13) as H16; simpl; lia. 
       }
       destruct H10 as [H10 _]. apply Z.divide_pos_le in H11; try lia. specialize (H2 p ltac:(lia)). tauto.
Qed.

Lemma lemma_19_4_a : forall p : Z,
  Znt.prime p -> p ≠ 3 -> p ≡ 1 (mod 3) \/ p ≡ -1 (mod 3).
Proof.
  intros p H1 H2. unfold mod_equiv. apply Z.mod_small_iff in H2 as H3; try lia. apply Z.mod_small_iff in H3; try lia.
Qed.