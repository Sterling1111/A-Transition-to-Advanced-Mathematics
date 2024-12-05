Set Warnings "-all".

(* Standard Library imports *)
From Coq Require Export 
  (* Real number theory *)
  Reals 
  Lra 
  Reals.ROrderedType
  Reals.Rdefinitions
  Reals.Raxioms
  Reals.Rfunctions
  Reals.SeqSeries
  Reals.Rtrigo
  Reals.Ranalysis
  
  (* Arithmetic *)
  ZArith
  QArith
  Arith.Arith
  Arith.PeanoNat
  Arith.Compare_dec
  Lia
  
  (* Sets and Lists *)
  Lists.List
  Sets.Ensembles
  Sets.Classical_sets
  Sets.Powerset
  Sets.Finite_sets
  Sets.Image
  
  (* Logic *)
  Logic.Classical
  Logic.ClassicalFacts
  Logic.Classical_Pred_Type
  Logic.Classical_Prop
  Logic.FunctionalExtensionality
  Logic.ClassicalChoice
  
  (* Utilities *)
  Program
  Orders
  Sorting
  Permutation
  Classes.Morphisms
  Relations.Relations.

(* Common notations *)
Export ListNotations.
Import EqNotations.

(* Open common scopes *)
Open Scope R_scope.
Open Scope nat_scope.

(* this could create inconsistency so in general dont do it. 
   However for this project I prefer convinience over consistency *)

Axiom univalence : forall (A B : Type), (A = B) <-> exists (f : A -> B) (g : B -> A),
  (forall x, g (f x) = x) /\ (forall y, f (g y) = y).

Axiom EquivThenEqual: prop_extensionality.