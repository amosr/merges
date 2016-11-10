(* Multiple inputs and outputs, full or empty reads *)
Require Import Merges.Tactics.
Require Import Merges.Map.


Require Import Merges.List.List.
Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.


Module Base.
Section Process.
  Variable Value : Set.

  Variable Stream : Set.
  Variable StreamEqDec : EqDec Stream.


  Inductive Proc :=
   | Get : Stream -> Proc -> Proc
   | Put : Stream -> Proc -> Proc
   | Choice : Proc -> Proc -> Proc
   | Done : Proc.

  Inductive Multi :=
   | Spawn : list Stream -> Proc -> Multi -> Multi
   | End.

  Inductive EvalProcOut : Proc -> Stream -> Proc -> Set :=
   | EPO'Put s p : EvalProcOut (Put s p) s p
   | EPO'ChoiceL l s l' r:
      EvalProcOut l s l' ->
      EvalProcOut (Choice l r) s l'
   | EPO'ChoiceR l r s r':
      EvalProcOut r s r' ->
      EvalProcOut (Choice l r) s r'.

  Inductive EvalProcIn : Stream -> Proc -> Proc -> Set :=
   | EPI'Put s p : EvalProcOut (Put s p) s p
   | EPO'ChoiceL l s l' r:
      EvalProcOut l s l' ->
      EvalProcOut (Choice l r) s (Choice l' r)
   | EPO'ChoiceR l r s r':
      EvalProcOut r s r' ->
      EvalProcOut (Choice l r) s (Choice l r').

  Inductive EvalMultiOut : Multi -> Stream -> Multi -> Set :=
   | EMO'Spawn ss p s p' m:
      In s ss ->
      EvalProcOut p s p' ->
      EvalMultiOut (Spawn ss p m) s (Spawn ss p' m)
   | EMO'Skip ss p s m m':
      EvalMultiOut m s m' ->
      EvalMultiOut (Spawn ss p m) s (Spawn ss p m').