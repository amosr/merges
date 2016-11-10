(* Stream programs with blocking pull.
   No option of pull finished or not, just wait until something new comes along.
 *)
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
  (* I don't think predicate needs the peek of the stream before pull *)
  Definition Pred := list Value -> list Value -> Prop.

  (* No heap or variables, just constant values *)
  Inductive Block : Type :=
   (* Pull, ignore value, but note whether something was pulled *)
   | BlockPull   : Label -> Block
   (* Push a constant value *)
   | BlockPush   : Value -> Label -> Block
   (* Jump to another label without doing anything *)
   | BlockJump   : Label -> Block.
  Hint Constructors Block.

  Variable Blocks : Label -> Block.
  Variable LabelPre  : Label -> Pred.

  Inductive EvalB : list Value -> list Value -> Label
                 -> list Value -> list Value -> Label -> Prop :=
   | EvalBPull l lok i iss os
      : Blocks l = BlockPull lok
     -> EvalB iss os l
              (iss++[i])  os lok

   | EvalBPush l push l' iss os
      : Blocks l = BlockPush push l'
     -> EvalB iss os l
              iss (os ++ [push]) l'

   | EvalBJump l l' iss os
      : Blocks l = BlockJump l'
     -> EvalB iss os l
              iss os l'
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

  Theorem EvalBs_Hoare l iss os
   (hEvB : EvalBs iss    os l)
         : LabelPre l iss os.
  Proof.
   !induction hEvB.
  Qed.
End Machine.

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
  (*
  Ltac Program_Block_destruct p l :=
    let pre := fresh "block_pre" in
    let eq  := fresh "block_eq" in
    destruct (Blocks p l) eqn:eq;
    lets pre: (BlocksPre p l);
    simpl;
    rewrite eq in *. *)
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
      (* try to run 1. for most it doesn't matter what state is, *)
      (* as state can only be 'Waiting' if stuck on a push. *)
      (* pulling is normal. *)
      | B.BlockPull lok, _, _, _
      => B.BlockPull (LX lok l2 Ok s2)

      (* trying to push while in 'Ok' marks this as 'Waiting' for other to pull *)
      | B.BlockPush _ _, _, Ok, _
      => B.BlockJump (LX l1 l2 Waiting s2)

      (* jump is normal *)
      | B.BlockJump l', _, _, _
      => B.BlockJump (LX l' l2 Ok s2)


      (* try to run 2 *)
      (* pulling while 'Ok' marks as waiting. *)
      | _, B.BlockPull _, _, Ok
      => B.BlockJump (LX l1 l2 s1 Waiting)

      (* pushing is normal *)
      | _, B.BlockPush f l', _, _
      => B.BlockPush f (LX l1 l' s1 Ok)

      (* jump is normal *)
      | _, B.BlockJump l', _, _
      => B.BlockJump (LX l1 l' s1 Ok)


      (* Both machines are waiting on other one, so can progress *)
      | B.BlockPush f1 l1', B.BlockPull lok, Waiting, Waiting
      => B.BlockJump (LX l1' lok Ok Ok)

      end
   end.

  Check P.EvalBs.
  Definition listOfOption (o : option nat) : list nat :=
  match o with
  | Some v => [v]
  | None   => []
  end.
  Definition LabelPre (l : L') : B.Pred :=
   match l with
   | LX l1 l2 s1 s2
   => fun iss os
   => exists (iss' : list nat),
      P.EvalBs P1 iss  iss' l1
   /\ P.EvalBs P2 iss' os l2
   end.
  Hint Unfold LabelPre.


  Program Definition r := {| P.Blocks := Blocks; P.LabelPre := LabelPre; P.Init := LX (P.Init P1) (P.Init P2) Ok Ok |}.
  Next Obligation.
   unfolds B.BlocksPreT.
   introv hEvBs hLbl hEvB.
   destruct l; destruct l'.
   !inverts hEvB; simpls
  ; destruct (P.Blocks P1 l1) eqn:P1Block
  ; destruct (P.Blocks P2 l2) eqn:P2Block
  ; destruct s1; destruct s2
  ; (!inject_all; simpls; tryfalse)
  ; try solve [(!jauto_set)
  ;   (!eapply B.EvalBs1)
  ;   try solve [!eapply B.EvalBPull]
  ;   try solve [!eapply B.EvalBPush]
  ;   try solve [!eapply B.EvalBJump]
  ].
  Qed.
  Next Obligation.
   jauto_set; eapply B.EvalBs0.
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