Require Import Merges.Tactics.
Require Import Merges.Map.

Require Import Merges.Machine.
Require Import Merges.Fusion.


Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.
Require Import Coq.Logic.FunctionalExtensionality.


Module Eg.
  Module Map.
    Module B := Base.
    Module P := Program.
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

    Definition LabelPre (l : L) : B.Pred C V :=
      match l with
      | L'Pull => fun iss h => iss Cout = map f (iss Cin)
      | L'Push => fun iss h => f (h V0) :: iss Cout = map f (iss Cin)
      | L'Release => fun iss h => iss Cout = map f (iss Cin)
      end.

    Definition StreamType (c : C) : B.StreamTypeT :=
      if EqDec_C c Cin
      then B.Input
      else if EqDec_C c Cout
      then B.Output
      else B.Ignore.

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

  Module EvalsB.
  Section EvalsB.
    Variable Label : Set.
    Variable ChanV : Set.
    Variable ScalarV : Set.

    Variable P : P.Program Label ChanV ScalarV.

    Inductive EvalsB : B.StreamHeap ChanV -> B.ScalarHeap ScalarV -> Label -> B.StreamHeap ChanV -> B.ScalarHeap ScalarV -> Label -> Prop :=
     | EvalsB0 l h sh
        : EvalsB h sh l   h sh l
     | EvalsB1 l l' l'' h h' h'' sh sh' sh''
        : B.EvalB (P.ChanVarEqDec P) (P.ScalarVarEqDec P) (P.StreamType P) (P.Blocks P) h sh l   h' sh' l'
       -> EvalsB h' sh' l'   h'' sh'' l''
       -> EvalsB h sh l   h'' sh'' l''
     .

    Definition EvalTop :=
     EvalsB (fun _ => []) (fun _ => 0) (P.Init P).

  End EvalsB. End EvalsB.

  Module Eg1.
    Inductive C := C1 | C2 | C3.
    Theorem EqDec_C : EqDec C. decides_equality. Qed.

    Module M := Map.

    Theorem C1_ne_C2 : C1 <> C2. Proof. intros X. inverts X. Qed.
    Theorem C2_ne_C3 : C2 <> C3. Proof. intros X. inverts X. Qed.

    Definition P1 := Map.P EqDec_C (fun x => S x) C1_ne_C2.
    Definition P2 := Map.P EqDec_C (fun x => S x) C2_ne_C3.

    Definition P' := r P1 P2 EqDec_C.

    Ltac sunfolds X := unfolds X; simpls.

    Theorem eval_P1_nil:
      exists sh,
     EvalsB.EvalTop P1
      (fun c => match c with
                | C1 => []
                | C2 => []
                | C3 => []
                end)
      sh Map.L'Pull.
    Proof.
     eexists. unfolds.
     applys_eq EvalsB.EvalsB0 3.
      extensionality c; !destruct c.
    Qed.


    Theorem eval_P1_2:
      exists sh,
     EvalsB.EvalTop P1
      (fun c => match c with
                | C1 => [1; 2]
                | C2 => [2; 3]
                | C3 => []
                end)
      sh Map.L'Pull.
    Proof.
     eexists. unfolds.
     eapply EvalsB.EvalsB1.
       !eapply B.EvalBPullOk; !simpls; !unfolds Map.StreamType.
        repeat !destruct (EqDec_C); tryfalse.

     eapply EvalsB.EvalsB1.
       !eapply B.EvalBPush; !simpls; !unfolds Map.StreamType;
        repeat !destruct (EqDec_C); tryfalse.

     eapply EvalsB.EvalsB1.
       !eapply B.EvalBRelease; !simpls; !unfolds Map.StreamType;
        repeat !destruct (EqDec_C); tryfalse.

     eapply EvalsB.EvalsB1.
       !eapply B.EvalBPullOk; !simpls; !unfolds Map.StreamType.
        repeat !destruct (EqDec_C); tryfalse.

     eapply EvalsB.EvalsB1.
       !eapply B.EvalBPush; !simpls; !unfolds Map.StreamType;
        repeat !destruct (EqDec_C); tryfalse.

     eapply EvalsB.EvalsB1.
       !eapply B.EvalBRelease; !simpls; !unfolds Map.StreamType;
        repeat !destruct (EqDec_C); tryfalse.

     applys_eq EvalsB.EvalsB0 3.
       extensionality c;
       !unfolds update.
        simpls.
        destruct c;
        repeat !destruct (EqDec_C); tryfalse.
        repeat !destruct (Map.P_obligation_1); tryfalse.
    Qed.


    Theorem eval_P'_1:
      exists sh,
     EvalsB.EvalTop P'
      (fun c => match c with
                | C1 => [11; 1]
                | C2 => [12; 2]
                | C3 => [    3]
                end)
      sh (F.LX Map.L'Pull Map.L'Pull (fun c : C => F.NoValue)
        (fun c : C =>
          match c with
          | C1 => F.NoValue
          | C2 => F.AvailableToPull
          | C3 => F.NoValue
          end) F.Valid).
    Proof.
     eexists. unfolds. simpls.

  Ltac ev X :=
       !eapply X; !simpls; !unfolds Map.StreamType; unfolds F.stateUpdate; unfolds update;
        repeat destruct (EqDec_C); tryfalse;
        try reflexivity;
        sunfolds F.StreamType;
        sunfolds Map.StreamType;
        repeat destruct (EqDec_C); !tryfalse.

     (* Pull Pull *)
     eapply EvalsB.EvalsB1.
       ev B.EvalBPullOk.
     (* Push Pull *)
     eapply EvalsB.EvalsB1.
       ev B.EvalBUpdate.
     (* Push Pull *)
     eapply EvalsB.EvalsB1.
       ev B.EvalBPush.
     (* Rele Pull *)
     eapply EvalsB.EvalsB1.
       ev B.EvalBRelease.
     (* Pull Pull *)
     eapply EvalsB.EvalsB1.
       ev B.EvalBPullOk.
     (* Push Pull *)
     eapply EvalsB.EvalsB1.
       ev B.EvalBUpdate.
     (* Push Push *)
     eapply EvalsB.EvalsB1.
       ev B.EvalBPush.
     (* Push Rele *)
     eapply EvalsB.EvalsB1.
       ev B.EvalBJump.
     (* Push Pull *)
     eapply EvalsB.EvalsB1.
       ev B.EvalBUpdate.
     (* Push Pull *)
     eapply EvalsB.EvalsB1.
       ev B.EvalBPush.
     (* Rele Pull *)
     eapply EvalsB.EvalsB1.
       ev B.EvalBRelease.

     applys_eq EvalsB.EvalsB0 0; !fequals.
      fequals; extensionality c; destruct c;
        repeat !destruct (EqDec_C); !tryfalse.

       extensionality c;
       !unfolds update.
        simpls.
        destruct c;
        repeat !destruct (EqDec_C); !tryfalse;
        repeat !destruct (FT.ScalarVarEqDec_V); tryfalse.
    Qed.

    (* XXX need to add 'priority' to fusion algorithm, so HaveValue Pull > NoValue Pull,
      so that evaluation order for above is more natural
     *)

  End Eg1.
End Eg.