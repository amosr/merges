(* (Are these the...) Simplest possible stream programs *)
Require Import Merges.Tactics.
Require Import Merges.Map.


Require Import Merges.List.List.
Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.
Require Import Coq.Logic.FunctionalExtensionality.


Module Base.
Section Machine.
  Variable Label : Set.

  Definition Value := nat.
  (* Pred input_seen input_left output *)
  Definition Pred := list Value -> list Value -> Prop.

  (* No heap or variables, just constant values *)
  Inductive Block : Type :=
   (* Pull, ignore value, but note whether something was pulled *)
   | BlockPull   : Label -> Label -> Block
   (* Push a constant value *)
   | BlockPush   : Value -> Label -> Block
   (* Jump to another label without doing anything *)
   | BlockJump   : Label -> Block
   (* End of program *)
   | BlockExit : Block.
  Hint Constructors Block.

  Variable Blocks : Label -> Block.
  Variable LabelPre  : Label -> Pred.


  Inductive EvalB : list Value -> list Value -> Label
                 -> list Value -> list Value -> Label -> Prop :=
   | EvalBPullOk l lok lno i iss os
      : Blocks l = BlockPull lok lno
     -> EvalB iss os l
              (iss++[i])  os lok

   | EvalBPullNo l lok lno iss os
      : Blocks l = BlockPull lok lno
     -> EvalB iss os l
              iss os lno


   | EvalBPush l push l' iss os
      : Blocks l = BlockPush push l'
     -> EvalB iss os l
              iss (os ++ [push]) l'

   | EvalBJump l l' iss os
      : Blocks l = BlockJump l'
     -> EvalB iss os l
              iss os l'

   | EvalBExitIgnore l i iss os
      : Blocks l = BlockExit
     -> EvalB iss os l
              (iss++[i]) os l
   .

  Variable Init : Label.
  Variable InitPre : LabelPre Init [] [].

  Inductive EvalBs : list Value -> list Value -> Label -> Prop :=
   | EvalBs0
      : EvalBs [] [] Init
   | EvalBs1 l l' iss iss' os os'
      : EvalBs iss os l
     -> EvalB  iss os l iss' os' l'
     -> EvalBs iss' os' l'
   .

  Definition BlocksPreT :=
    forall iss iss' os os' l l',
    EvalBs iss os l ->
    LabelPre l iss os ->
    EvalB  iss os l iss' os' l' ->
    LabelPre l' iss' os'.

  Hypothesis BlocksPre: BlocksPreT.

  Theorem EvalB_Step l iss os
         : exists l' iss' os'
         , EvalB iss  os  l
                 iss' os' l'.
  Proof.
   Ltac CTOR C := !repeat eexists; eapply C.

   destruct (Blocks l) eqn:eql; tryfalse.
    CTOR EvalBPullNo.
    CTOR EvalBPush.
    CTOR EvalBJump.
    exists l (iss ++ [0]) os.
    !apply EvalBExitIgnore.
  Qed.


  Theorem EvalBs_Hoare l iss os
   (hEvB : EvalBs iss os l)
         : LabelPre l iss os.
  Proof.
   !induction hEvB.
  Qed.
End Machine.

Section Functor.
  Definition Block_map_L {A B : Set} (f : A -> B) (b : Block A) : Block B :=
   match b with
   | BlockPull lok lno => BlockPull (f lok) (f lno)
   | BlockPush vv l      => BlockPush vv (f l)
   | BlockJump l      => BlockJump  (f l)
   | BlockExit _       => BlockExit _
   end.
End Functor.

End Base.

Module Program.
 Module B := Base.
 Record Program (Label : Set) : Type
  := mkProgram
   { Init     : Label
   ; Blocks   : Label -> B.Block Label
   ; LabelPre : Label -> B.Pred
   ; BlocksPre: B.BlocksPreT Blocks LabelPre Init
   ; InitPre  : LabelPre Init [] []
   }.

  Definition EvalBs (Label : Set) (P : Program Label)
   := B.EvalBs (Blocks P) (Init P).
End Program.


Module Fuse.
  Module B := Base.
  Module P := Program.

  Parameter L1 : Set.
  Parameter P1 : P.Program L1.

  Parameter L2 : Set.
  Parameter P2 : P.Program L2.

  Inductive State :=
    | Waiting
    | Ok
    .
  Hint Constructors State.

  Inductive L' :=
    | LX (l1 : L1) (l2 : L2) (s1 : State) (s2 : State).
  Hint Constructors L'.

  Definition Blocks (l : L') : B.Block L' :=
   match l with
   | LX l1 l2 s1 s2
   => match P.Blocks P1 l1, P.Blocks P2 l2, s1, s2 with
      (* Both machines are done, might as well finish *)
      | B.BlockExit _, B.BlockExit _, _, _
      => B.BlockExit _

      (* 1 trying to push but 2 is finished, so just skip ahead *)
      | B.BlockPush f1 l1', B.BlockExit _, _, _
      => B.BlockJump (LX l1' l2 Ok Ok)

      (* 2 trying to read but 1 is finished, so skip to end case *)
      | B.BlockExit _, B.BlockPull _ lno, _, _
      => B.BlockJump (LX l1 lno Ok Ok)

      (* try to run 1. for most it doesn't matter what state is, *)
      (* as state can only be 'Waiting' if stuck on a push. *)
      (* pulling is normal. *)
      | B.BlockPull lok lno, _, _, _
      => B.BlockPull (LX lok l2 Ok s2) (LX lno l2 Ok s2)

      (* trying to push while in 'Ok' marks this as 'Waiting' for other to pull *)
      | B.BlockPush _ _, _, Ok, _
      => B.BlockJump (LX l1 l2 Waiting s2)

      (* jump is normal *)
      | B.BlockJump l', _, _, _
      => B.BlockJump (LX l' l2 Ok s2)


      (* try to run 2 *)
      (* pulling while 'Ok' marks as waiting. *)
      | _, B.BlockPull _ _, _, Ok
      => B.BlockJump (LX l1 l2 s1 Waiting)

      (* pushing is normal *)
      | _, B.BlockPush f l', _, _
      => B.BlockPush f (LX l1 l' s1 Ok)

      (* jump is normal *)
      | _, B.BlockJump l', _, _
      => B.BlockJump (LX l1 l' s1 Ok)


      (* Both machines are waiting on other one, so can progress *)
      | B.BlockPush f1 l1', B.BlockPull lok _, Waiting, Waiting
      => B.BlockJump (LX l1' lok Ok Ok)

      end
   end.

  Definition LabelPre (l : L') : B.Pred :=
   match l with
   | LX l1 l2 _ _
   => fun iss os
   => exists iss',
      P.EvalBs P1 iss  iss' l1
   /\ P.EvalBs P2 iss' os   l2
   end.
  Hint Unfold LabelPre.


  Program Definition r := {| P.Blocks := Blocks; P.LabelPre := LabelPre; P.Init := LX (P.Init P1) (P.Init P2) Ok Ok |}.
  Next Obligation.
   Ltac doit X := try solve [(!eapply B.EvalBs1); (!eapply X)].

   unfolds B.BlocksPreT.
   introv hEvBs hLbl hEvB.
   destruct l; destruct l'.
   !inverts hEvB; simpls;
    try ( destruct (P.Blocks P1 l1) eqn:P1Block
        ; destruct (P.Blocks P2 l2) eqn:P2Block
        ; destruct s1; destruct s2
        );

    inject_all; simpls; tryfalse; jauto_set;
     doit B.EvalBPullOk;
     doit B.EvalBPullNo;
     doit B.EvalBPush;
     doit B.EvalBJump;
     doit B.EvalBExitIgnore;
     try assumption.

   destruct (P.Blocks P1 l0) eqn:P1Block
  ; destruct (P.Blocks P2 l3) eqn:P2Block
  ; destruct s0
  ; destruct s3
  ; tryfalse
  ; doit B.EvalBExitIgnore.
  Qed.
  Next Obligation.
   repeat eexists; constructor.
  Qed.


  Theorem fuse_ok (l1 : L1) (l2 : L2) (s1 s2 : State) iss oss:
   P.EvalBs r iss oss (LX l1 l2 s1 s2)
  ->
   exists (iss' : list nat),
      P.LabelPre P1 l1 iss  iss' /\ P.LabelPre P2 l2 iss' oss.
  Proof.
   introv hEvBs.
   apply B.EvalBs_Hoare with (LabelPre := LabelPre) in hEvBs.
   simpls; jauto_set.
   !apply B.EvalBs_Hoare with (LabelPre := P.LabelPre P1) in H.
   apply (P.InitPre P1).
   apply (P.BlocksPre P1).

   !apply B.EvalBs_Hoare with (LabelPre := P.LabelPre P2) in H0.
   apply (P.InitPre P2).
   apply (P.BlocksPre P2).

   apply (P.InitPre r).
   apply (P.BlocksPre r).
  Qed.
End Fuse.