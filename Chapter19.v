Require Import ZArith Lia Classical Reals Lra Classical_sets List String
               Ensembles QArith ClassicalFacts Finite_sets Powerset Finite_sets_facts Image 
               NArith DecimalString DecimalNat DecimalNat Decimal
               Fibonacci Sums Sets Binomial QRT WI_SI_WO Prime.

Require Export Chapter18.

Import ListNotations SetNotations Choose_Notations.

Open Scope Z_scope.

Module Znt := ZArith.Znumtheory.

Compute Z.sqrt 100.

Fixpoint element_divides (z : Z) (l : list Z) : bool := 
  match l with 
  | [] => false
  | h :: t => if Z.eqb (Z.rem z h) 0 then true else element_divides z t
  end.

Searchy Z.rem.

Lemma element_divides_correct : forall z l, element_divides z l = true -> exists x, In x l /\ (x | z).
Proof.
  intros z l H1. induction l as [| h t IH].
  - inversion H1.
  - simpl in H1. destruct (Z.rem z h =? 0) eqn:Heq.
    -- assert (h = 0 \/ h <> 0) as [H2 | H2]; assert (z = 0 \/ z <> 0) as [H3 | H3]; try lia; subst.
       * exists 0. split. left. reflexivity. apply Z.divide_0_r.
       * 
Qed.

Compute element_divides 100 [3].
  

Fixpoint find_primes_le (z : Z) (l : list Z) : list Z := 

  