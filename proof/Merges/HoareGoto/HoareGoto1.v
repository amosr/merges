Require Import Merges.Tactics.
Require Import Merges.Map.


Require Import Merges.List.List.
Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.

Module Type Var.
 Variable Var   : Set.
 Variable VarEqDec : EqDec Var.

 Definition update t := Map.update Var t VarEqDec.
 Hint Unfold update.

End Var.

Module Type Label.
 Variable Label      : Set.
 Variable LabelEqDec : EqDec Label.
End Label.

Module Program (V : Var) (L : Label).
  Definition Value := nat.
  Definition Heap := Map V.Var Value.
  Definition Pred := Heap -> Prop.

  Definition predUpdate v f (p : Pred)
    := fun s => p (V.update v (f (s v)) s).
  Hint Unfold predUpdate.

  Definition predImplies (p1 p2 : Pred)
    := forall s, p1 s -> p2 s.
  Hint Unfold predImplies.


  Inductive Instr : Type :=
     IInc : V.Var -> Instr
   | IDec : V.Var -> Instr
  .
  Hint Constructors Instr.

  Definition InstrPre (i : Instr) (post : Pred) : Pred :=
   match i with
   | IInc v => predUpdate v (fun n => S n)    post
   | IDec v => predUpdate v (fun n => pred n) post
   end.
  Hint Unfold InstrPre.



  Inductive Block : Type :=
     BlockJump : L.Label -> Instr -> Block
   | BlockJZ   : V.Var -> L.Label -> L.Label -> Block
   | BlockExit : Block.
  Hint Constructors Block.

  Variable Blocks : L.Label -> Block.
  Variable LabelPre  : L.Label -> Pred.

  Definition BlockPre (l : L.Label) (b : Block) : Prop :=
    match b with
     | BlockJump l' i
     => predImplies (LabelPre l) (InstrPre i (LabelPre l'))
     /\ predImplies (InstrPre i (LabelPre l')) (LabelPre l')

     | BlockJZ v lz lnz
     => predImplies (fun s => LabelPre l s /\ s v  = 0) (LabelPre lz)
     /\ predImplies (fun s => LabelPre l s /\ s v <> 0) (LabelPre lnz)

     | BlockExit
     => True
    end.
  Hint Unfold BlockPre.

  Hypothesis BlocksPre: forall l, BlockPre l (Blocks l).


  Inductive EvalI : Heap -> Instr -> Heap -> Prop :=
   | EvalIInc v s
      : EvalI s (IInc v) (V.update v (S (s v)) s)
   | EvalIDec v s
      : EvalI s (IDec v) (V.update v (pred (s v)) s).
  Hint Constructors EvalI.

  Inductive EvalB : Heap -> L.Label -> Heap -> L.Label -> Prop :=
   | EvalBJump l l' i s s'
      : Blocks l = BlockJump l' i
     -> EvalI s i s'
     -> EvalB s l s' l'
   | EvalBJZ'Z v l lz lnz s
      : Blocks l = BlockJZ v lz lnz
     -> s v = 0
     -> EvalB s l s lz
   | EvalBJZ'NZ v l lz lnz s
      : Blocks l = BlockJZ v lz lnz
     -> s v <> 0
     -> EvalB s l s lnz.
  Hint Constructors EvalB.

  Theorem EvalI_Hoare i s s' post
   (hPre : InstrPre i post s)
   (hEvI : EvalI s i s')
         : post s'.
  Proof.
   induction~ hEvI.
  Qed.

  Theorem BlockPre_Get l b
    : Blocks l = b
   -> BlockPre l b.
  Proof.
    intros.
    rewrite <- H.
    apply BlocksPre.
  Qed.
  Hint Immediate BlockPre_Get.

  Theorem EvalB_Hoare l l' s s'
   (hPre : LabelPre l s)
   (hEvB : EvalB s l s' l')
         : LabelPre l' s'.
  Proof.
   induction~ hEvB;
    destructs~ (BlockPre_Get H).
    eapply EvalI_Hoare; eauto.
  Qed.



  Inductive EvalBs : Heap -> L.Label -> Heap -> L.Label -> Prop :=
   | EvalBs0 l s
      : Blocks l = BlockExit
     -> EvalBs s l s l
   | EvalBs1 l s l' s' l'' s''
      : EvalB  s l s' l'
     -> EvalBs s' l' s'' l''
     -> EvalBs s l s'' l''.
  Hint Constructors EvalB.


  Theorem EvalBs_Hoare l l' s s'
   (hPre : LabelPre l s)
   (hEvB : EvalBs s l s' l')
         : LabelPre l' s'.
  Proof.
   induction~ hEvB.
    apply EvalB_Hoare in H; eauto.
  Qed.

End Program.
