(* Turn off common noisy warnings *)
Set Warnings "-ambiguous-paths".
Set Warnings "-uniform-inheritance".
Set Warnings "-notation-overridden".
Set Warnings "-parsing".
Set Warnings "-deprecated-hint-without-locality".

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
  Logic.Classical_Pred_Type
  Logic.Classical_Prop
  Logic.FunctionalExtensionality
  
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