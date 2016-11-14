Require Import Merges.Tactics.
Require Import Merges.Map.

Require Import Merges.Machine.
Require Import Merges.Fusion.
Require Import Merges.Example.Base.


Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.
Require Import Coq.Logic.FunctionalExtensionality.

Module B := Base.
Module P := Program.

Module Map.
Section Map.
  Variable C : Set.
  Variable Cin : C.
  Variable Cout : C.
  Variable EqDec_C : EqDec C.

  Variable f : B.Value -> B.Value.
  Variable Cin_ne_Cout : Cin <> Cout.

  Inductive V :=
    | V0 : V.

  Inductive L :=
    | L'Pull : L
    | L'Push : L
    | L'Release : L.

  Definition Blocks (l : L) : B.Block L C V :=
    match l with
    | L'Pull => B.BlockPull V0 Cin L'Push
    | L'Push => B.BlockPush Cout (fun sh => f (sh V0)) L'Release
    | L'Release => B.BlockRelease V Cin L'Pull
    end.
  Hint Unfold Blocks.

  Definition LabelPre (l : L) : B.Pred C V :=
    match l with
    | L'Pull => fun iss h => iss Cout = map f (iss Cin)
    | L'Push => fun iss h => f (h V0) :: iss Cout = map f (iss Cin)
    | L'Release => fun iss h => iss Cout = map f (iss Cin)
    end.
  Hint Unfold LabelPre.

  Definition StreamType (c : C) : B.StreamTypeT :=
    if EqDec_C c Cin
    then B.Input
    else if EqDec_C c Cout
    then B.Output
    else B.Ignore.
  Hint Unfold StreamType.

  Program Definition P : P.Program L C V :=
    {| P.Init := L'Pull
    ; P.Blocks := Blocks
    ; P.ChanVarEqDec := EqDec_C
    ; P.StreamType := StreamType
    ; P.LabelPre := LabelPre
    |}.
  Next Obligation.
    decides_equality.
  Qed.
  Next Obligation.
    unfolds B.BlocksPreT. unfolds LabelPre. unfolds Blocks.
    introv hLbl hEvB.
    hint Cin_ne_Cout.

    !inverts hEvB; try destruct l; try destruct l'; inject_all; tryfalse.
    all: unfolds update; unfolds StreamType.

    all: try destruct v.
    all: matchmaker_goal'.
    !rewrite hLbl.
    !destruct n0.
  Qed.
End Map. End Map.
