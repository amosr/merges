(* Multiple inputs and outputs, blocking reads *)
Require Import Merges.Tactics.
Require Import Merges.Map.

Require Import Merges.Machine.
Require Import Merges.Fusion.Base.
Require Import Merges.Fusion.Tactics.


Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.
Require Import Coq.Logic.FunctionalExtensionality.


  Module B := Machine.Base.
  Module P := Machine.Program.
  Module F := Base.Fuse.
  Module FT := Tactics.Tactics.

Section Proof.
  Variable C : Set.
  Variable V1 : Set.
  Variable L1 : Set.
  Variable P1 : P.Program L1 C V1.

  Variable V2 : Set.
  Variable L2 : Set.
  Variable P2 : P.Program L2 C V2.

  Variable EqDec_C : EqDec C.

  Theorem EvalBlockPull pV pC pL:
   FT.EvalStep P1 P2 EqDec_C
    (B.BlockPull pV pC pL).
  Proof.
    EvalStep_intros.
    EvalStep_unfold_all.
    jauto_set.
      (* EvalBs P1 *)
      - matchmaker hBlockEq; inject_all.

        all: try EvalStep_Rule hEv1 hSv1.
        all: !eapply B.EvalBs1.
        all: try EvalStep_Rule B.EvalBPullOk hSv1.
        all: try EvalStep_Rule B.EvalBIgnore hSv1.

      (* Sv P1 *)
      - EvalStep_Invariant hSv1 hBlockEq.

      (* EvalBs P2 *)
      - matchmaker hBlockEq; inject_all.

        all: try EvalStep_Rule hEv2 hSv2.
        all: !eapply B.EvalBs1.
        all: try EvalStep_Rule B.EvalBPullOk hSv2.
        all: try EvalStep_Rule B.EvalBIgnore hSv2.

      (* Sv P2 *)
      - EvalStep_Invariant hSv2 hBlockEq.

        all: rewrite H1; fequals; extensionality v2; matchmaker_goal'.
    Qed.

End Proof.
