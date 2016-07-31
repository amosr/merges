Require Import Merges.Tactics.
Require Import Merges.Map.


Require Import Merges.List.List.
Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.
Require Import Coq.Logic.FunctionalExtensionality.


Module Base.
Section Machine.
 Variable Var : Set.
 Variable VarEqDec : EqDec Var.
 Variable Label : Set.

 Definition Value := nat.
 Definition Heap := Map Var Value.
 (* Pred heap input_seen input_left output *)
 Definition Pred := Heap -> list Value -> list Value -> list Value -> Prop.

 Let varUpdate := Map.update Var Value VarEqDec.

  Inductive Block : Type :=
   | BlockPull   : Var -> Label -> Label -> Block
   | BlockPush   : (Heap -> Value) -> Label -> Block
   | BlockUpdate : Var -> (Heap -> Value) -> Label -> Block
   | BlockJump   : Label -> Block
   (* To add for next one:
   | BlockIf     : (Heap -> bool) -> Label -> Label -> Block
   *)
   | BlockExit : Block.
  Hint Constructors Block.

  Variable Blocks : Label -> Block.
  Variable LabelPre  : Label -> Pred.

  Definition BlockPre (l : Label) (b : Block) : Prop :=
    match b with
     | BlockPull v lok lno
     => (forall s x iss isr os, LabelPre l s iss (x::isr) os -> LabelPre lok (varUpdate v x s) (iss ++ [x]) isr os)
     /\ (forall s iss os, LabelPre l s iss [] os -> LabelPre lno s iss [] os)

     | BlockPush push l'
     => (forall s iss isr os, LabelPre l s iss isr os -> LabelPre l' s iss isr (os ++ [push s]))

     | BlockUpdate v f l'
     => (forall s iss isr os, LabelPre l s iss isr os -> LabelPre l' (varUpdate v (f s) s) iss isr os)

     | BlockJump l'
     => (forall s iss isr os, LabelPre l s iss isr os -> LabelPre l' s iss isr os)

     | BlockExit
     => True
    end.
  Hint Unfold BlockPre.

  Hypothesis BlocksPre: forall l, BlockPre l (Blocks l).


  Inductive EvalB : Heap -> list Value -> list Value -> list Value -> Label
                 -> Heap -> list Value -> list Value -> list Value -> Label -> Prop :=
   | EvalBPullOk l v lok lno s i iss isr os
      : Blocks l = BlockPull v lok lno
     -> EvalB s iss (i::isr) os l
              (varUpdate v i s)    (iss++[i]) isr  os lok

   | EvalBPullNo l v lok lno s iss os
      : Blocks l = BlockPull v lok lno
     -> EvalB s    iss [] os l
              s    iss [] os lno


   | EvalBPush l push l' s iss isr os
      : Blocks l = BlockPush push l'
     -> EvalB s    iss isr os l
              s    iss isr (os ++ [push s]) l'


   | EvalBUpdate l v f l' s iss isr os
      : Blocks l = BlockUpdate v f l'
     -> EvalB s iss isr os l
              (varUpdate v (f s) s) iss isr os l'



   | EvalBJump l l' s iss isr os
      : Blocks l = BlockJump l'
     -> EvalB s    iss isr os l
              s    iss isr os l'
   .

  Theorem BlockPre_Get l b
   (hBlock : Blocks l = b)
           : BlockPre l b.
  Proof.
    !rewrite <- hBlock.
  Qed.
  Hint Immediate BlockPre_Get.

  Theorem EvalB_Hoare l l' s s' iss iss' isr isr' os os'
   (hPre : LabelPre l s iss isr os)
   (hEvB : EvalB s iss isr os l
                 s' iss' isr' os' l')
         : LabelPre l' s' iss' isr' os'.
  Proof.
   !induction hEvB;
      try destructs (BlockPre_Get H);
      forwards: (BlockPre_Get H).
  Qed.

  Theorem EvalB_Step l s iss isr os
   (hNotExit : Blocks l <> BlockExit)
         : exists l' s' iss' isr' os'
         , EvalB s  iss  isr  os  l
                 s' iss' isr' os' l'.
  Proof.
   Ltac CTOR C := !repeat eexists; eapply C.

   destruct (Blocks l) eqn:eql; tryfalse.
    destruct isr.
      CTOR EvalBPullNo.
      CTOR EvalBPullOk.
    CTOR EvalBPush.
    CTOR EvalBUpdate.
    CTOR EvalBJump.
  Qed.

  Inductive EvalBs : Heap -> list Value -> list Value -> list Value -> Label
                  -> Heap -> list Value -> list Value -> list Value -> Label -> Prop :=
   | EvalBs0 l s iss isr os
      : Blocks l = BlockExit
     -> EvalBs s iss isr os l s iss isr os l
   | EvalBs1 l l' l'' s s' s'' iss iss' iss'' isr isr' isr'' os os' os''
      : EvalBs s iss isr os l s' iss' isr' os' l'
     -> EvalB  s' iss' isr' os' l' s'' iss'' isr'' os'' l''
     -> EvalBs s iss isr os l s'' iss'' isr'' os'' l''.


  Theorem EvalBs_Hoare l l' s s' iss iss' isr isr' os os'
   (hPre : LabelPre l s iss isr os)
   (hEvB : EvalBs s  iss  isr  os l
                  s' iss' isr' os' l')
         : LabelPre l' s' iss' isr' os'.
  Proof.
   hint EvalB_Hoare.
   !induction hEvB.
  Qed.

  (* Cannot prove this without termination variants.
     Is it necessary? *)
  (* Theorem EvalBs_Step l s is os
         : exists l' s' is' os'
         , EvalBs s is os l
                 s' is' os' l'.
   *)

End Machine.

Section Functor.
  Definition Block_map_V {L A B : Set}
    (f : A -> B) (b : Block A L) : Block B L :=
   match b with
   | BlockPull v lok lno => BlockPull (f v) lok lno
   | BlockPush vv l      => BlockPush (fun h => vv (fun x => h (f x))) l
   | BlockUpdate v vv l  => BlockUpdate (f v) (fun h => vv (fun x => h (f x))) l
   | BlockJump _  l      => BlockJump _ l
   | BlockExit _ _       => BlockExit _ _
   end.
  Definition Block_map_L {V A B : Set} (f : A -> B) (b : Block V A) : Block V B :=
   match b with
   | BlockPull v lok lno => BlockPull v (f lok) (f lno)
   | BlockPush vv l      => BlockPush vv (f l)
   | BlockUpdate v vv l  => BlockUpdate v vv (f l)
   | BlockJump _  l      => BlockJump _  (f l)
   | BlockExit _ _       => BlockExit _ _
   end.

  Theorem Heap_comap_V {A B : Set} (f : B -> A) (h : Heap A) : Heap B.
    firstorder.
  Defined.

  Definition Heap_fun_map_V {A B C : Set}
      (inj : A -> B)
      (fh : Heap A -> C)
      (h : Heap B) : C
    := fh (fun x => h (inj x)).
End Functor.

End Base.

Module Program.
 Module B := Base.

 Record Program (Var Label : Set) : Type
  := mkProgram
   { VarEqDec : EqDec Var
   ; Init     : Label
   ; Blocks   : Label -> B.Block Var Label
   ; LabelPre : Label -> B.Pred Var
   ; BlocksPre: (forall l : Label, B.BlockPre VarEqDec LabelPre l (Blocks l))
   ; InitPre  : forall s is, LabelPre Init s [] is []
   (* (* TODO this is necessary for it. maybe isr should not be in Pred *)
   ; ExtendPre: forall l s iss isr os v
              , LabelPre l s iss isr os
             -> LabelPre l s iss (isr++[v]) os
   *)
   }.

  Definition EvalFromInit (Var Label : Set) (p : Program Var Label)
        (isr : list B.Value)
    := B.EvalBs (VarEqDec p) (Blocks p) (fun _ => 0) [] isr [] (Init p).

  Ltac Program_Block_destruct p l :=
    let pre := fresh "block_pre" in
    let eq  := fresh "block_eq" in
    destruct (Blocks p l) eqn:eq;
    lets pre: (BlocksPre p l);
    simpl;
    rewrite eq in *.
End Program.

Module ProgramId.
  Module B := Base.

  Inductive V : Set := V1.
  Inductive L := L0 | L1 | L2.

  Definition Blocks (l : L) : B.Block V L :=
   match l with
   | L0 => B.BlockPull V1 L1 L2
   | L1 => B.BlockPush (fun s => s V1) L0
   | L2 => B.BlockExit V L
   end.
  Definition LabelPre (l : L) : B.Pred V :=
   match l with
   | L0 => fun h iss isr os => iss = os
   | L1 => fun h iss isr os => iss = os ++ [h V1]
   | L2 => fun h iss isr os => isr = []
   end.

  Program Definition r := {| Program.Blocks := Blocks; Program.LabelPre := LabelPre; Program.Init := L0 |}.
  Next Obligation.
    decides_equality.
  Defined.
  Next Obligation.
   hint update_eq_is.
   destruct l; simpls; firstorder; congruence.
  Qed.
End ProgramId.

Module ProgramMap.
  Module B := Base.

  Parameter f : B.Value -> B.Value.
  Inductive V : Set := V1.
  Inductive L := L0 | L1 | L2.

  Definition Blocks (l : L) : B.Block V L :=
   match l with
   | L0 => B.BlockPull V1 L1 L2
   | L1 => B.BlockPush (fun s => f (s V1)) L0
   | L2 => B.BlockExit V L
   end.
  Definition LabelPre (l : L) : B.Pred V :=
   match l with
   | L0 => fun h iss isr os => map f iss = os
   | L1 => fun h iss isr os => map f iss = os ++ [f (h V1)]
   | L2 => fun h iss isr os => isr = []
   end.

  Program Definition r := {| Program.Blocks := Blocks; Program.LabelPre := LabelPre; Program.Init := L0 |}.
  Next Obligation.
    decides_equality.
  Defined.
  Next Obligation.
   destruct l; simpls; firstorder.

    rewrite map_app; simpl.
    rewrite update_eq_is.
    congruence.
  Qed.
End ProgramMap.


Module Fuse.
  Module B := Base.
  Module P := Program.

  Parameter V1 L1 : Set.
  Parameter P1 : P.Program V1 L1.

  Parameter V2 L2 : Set.
  Parameter P2 : P.Program V2 L2.
  Inductive V' := V'1 (v : V1) | V'2 (v : V2).
  Hint Constructors V'.

  Inductive State :=
    | Waiting
    | Ok
    .
  Hint Constructors State.

  Inductive L' :=
    | LX (l1 : L1) (l2 : L2) (s1 : State) (s2 : State).
  Hint Constructors L'.

  Definition Blocks (l : L') : B.Block V' L' :=
   match l with
   | LX l1 l2 s1 s2
   => match P.Blocks P1 l1, P.Blocks P2 l2, s1, s2 with
      (* Both machines are done, might as well finish *)
      | B.BlockExit _ _, B.BlockExit _ _, _, _
      => B.BlockExit _ _

      (* 1 trying to push but 2 is finished, so just skip ahead *)
      | B.BlockPush f1 l1', B.BlockExit _ _, _, _
      => B.BlockJump _ (LX l1' l2 Ok Ok)

      (* 2 trying to read but 1 is finished, so skip to end case *)
      | B.BlockExit _ _, B.BlockPull _ _ lno, _, _
      => B.BlockJump _ (LX l1 lno Ok Ok)

      (* try to run 1. for most it doesn't matter what state is, *)
      (* as state can only be 'Waiting' if stuck on a push. *)
      (* pulling is normal. *)
      | B.BlockPull v1 lok lno, _, _, _
      => B.BlockPull (V'1 v1) (LX lok l2 Ok s2) (LX lno l2 Ok s2)

      (* trying to push while in 'Ok' marks this as 'Waiting' for other to pull *)
      | B.BlockPush _ _, _, Ok, _
      => B.BlockJump _ (LX l1 l2 Waiting s2)

      (* update just needs to work over super heap *)
      | B.BlockUpdate v f l', _, _, _
      => B.BlockUpdate (V'1 v) (B.Heap_fun_map_V V'1 f) (LX l' l2 s1 s2)

      (* jump is normal *)
      | B.BlockJump _ l', _, _, _
      => B.BlockJump _ (LX l' l2 Ok s2)


      (* try to run 2 *)
      (* pulling while 'Ok' marks as waiting. *)
      | _, B.BlockPull _ _ _, _, Ok
      => B.BlockJump _ (LX l1 l2 s1 Waiting)

      (* pushing is normal *)
      | _, B.BlockPush f l', _, _
      => B.BlockPush (B.Heap_fun_map_V V'2 f) (LX l1 l' s1 Ok)

      (* update just needs to work over super heap *)
      | _, B.BlockUpdate v f l', _, _
      => B.BlockUpdate (V'2 v) (B.Heap_fun_map_V V'2 f) (LX l1 l' s1 Ok)

      (* jump is normal *)
      | _, B.BlockJump _ l', _, _
      => B.BlockJump _ (LX l1 l' s1 Ok)


      (* Both machines are waiting on other one, so can progress *)
      | B.BlockPush f1 l1', B.BlockPull v2 lok _, Waiting, Waiting
      => B.BlockUpdate (V'2 v2)
          (B.Heap_fun_map_V V'1 f1)
          (LX l1' lok Ok Ok)

      end
   end.

  Definition LabelPre (l : L') : B.Pred V' :=
   match l with
   | LX l1 l2 _ _
   => fun s iss isr os
   => forall iss' isr',
      P.EvalFromInit P1 (iss++isr) (B.Heap_comap_V V'1 s) iss isr (iss'++isr') l1
   -> P.EvalFromInit P2 (iss'++isr') (B.Heap_comap_V V'2 s) iss' isr' os l2
   -> (  P.LabelPre P1 l1 (B.Heap_comap_V V'1 s) iss  isr  (iss' ++ isr')
      /\ P.LabelPre P2 l2 (B.Heap_comap_V V'2 s) iss' isr' os )
   end.
  Hint Unfold LabelPre.

  (* After this we should be able to prove:

      Theorem fuse_vert_ok iss oss uss:
        EvalBs P1 iss oss ->
        EvalBs P2 oss uss ->
        EvalBs r  iss uss.

     Was talking to Ben about how to state general fusion (not just vertical or horizontal).
     But if we just prove that both programs' invariants are upheld, we could make a meta
     argument that the fusion is OK..

  *)

  Program Definition r := {| P.Blocks := Blocks; P.LabelPre := LabelPre; P.Init := LX (P.Init P1) (P.Init P2) Ok Ok |}.
  Next Obligation.
    hint (P.VarEqDec P1).
    hint (P.VarEqDec P2).
    decides_equality.
  Qed.
  Next Obligation.
  Ltac apply_with_vengeance H :=
    let zz := fresh "ext" in
    (!applys_eq H 0);
    try (!fequals; unfolds; extensionality zz; destruct_t (EqDec V'); destruct_t (EqDec V1); destruct_t (EqDec V2); try congruence).

   destruct l.
  Admitted.
  Next Obligation.
  Admitted.
(*
    P.Program_Block_destruct P1 l1.
     +
      simpls; splits; intros; splits; destructs block_pre.
      - apply_with_vengeance H2.
        destruct (H iss' isr').
        unfold P.EvalFromInit.
        inverts H0. destruct iss; tryfalse.
        applys_eq H4 0. fequals.
          !rewrite <- app_assoc.
*)
(*

      apply_with_vengeance H0.

      intros.
      repeat destruct H.
      destructs block_pre.
      eapply LabelPre__LabelPre.
      apply_with_vengeance H2.
      apply_with_vengeance H0.

    P.Program_Block_destruct P2 l2.
      destruct s1.
        destruct s2.
          simpls.
          intros.
          repeat destruct H.
          destructs block_pre0.
          eapply LabelPre__LabelPre.
          apply_with_vengeance block_pre.
          apply_with_vengeance H1.
          apply_with_vengeance H0.
          !fequals. eauto.
          !applys_eq H1 0. unfolds. eassumption.
          apply_with_vengeance H1.


      !applys_eq H2 0.

      unfold update. extensionality y.
      eapply H1.
      hint LabelPre__LabelPre.

      destructs block_pre.
      splits; intros; jauto_set.
      apply H.
      repeat eexists.
      destruct H. destruct e.

    Ltac SOLVEUPDATE :=
      eapply P.LabelPre_rewrite; eauto;
        extensionality x;
        unfold update;
        destruct r_obligation_1;
        try destruct P.VarEqDec; congruence.
    Ltac TICKY := !simpls; unfolds LabelPreAnd; unfolds PredAnd;
                   splits; intros; jauto_set.

    Ltac APPLIES:=
        try match goal with
        | [ F : _ |- _ ]
        => match goal with
          | [ X : _ |- _ ]
          => apply F in X
          end
        | [ F : _ |- _ ]
        => apply F
        end.

   destruct l.
    !P.Program_Block_destruct P1 l1.
      destruct i; TICKY; APPLIES; SOLVEUPDATE.
      TICKY.

    !P.Program_Block_destruct P2 l2.
      destruct i; TICKY; APPLIES; SOLVEUPDATE.
      TICKY.
 Qed.



*)


End Fuse.