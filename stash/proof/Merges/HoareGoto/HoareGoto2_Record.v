Require Import Merges.Tactics.
Require Import Merges.Map.


Require Import Merges.List.List.
Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.
Require Import Coq.Logic.FunctionalExtensionality.


Module Base.
Section Goto.
 Variable Var : Set.
 Variable VarEqDec : EqDec Var.
 Variable Label : Set.

 Definition Value := nat.
 Definition Heap := Map Var Value.
 Definition Pred := Heap -> Prop.

 Let varUpdate := Map.update Var Value VarEqDec.
 Let predUpdate v f (p : Pred)
    := fun s => p (varUpdate v (f (s v)) s).

 Let predImplies (p1 p2 : Pred)
    := forall s, p1 s -> p2 s.


  Inductive Instr : Type :=
   | IInc : Var -> Instr
   | IDec : Var -> Instr
   | INop : Instr
  .
  Hint Constructors Instr.

  Let InstrPre (i : Instr) (post : Pred) : Pred :=
   match i with
   | IInc v => predUpdate v (fun n => S n)    post
   | IDec v => predUpdate v (fun n => pred n) post
   | INop   => post
   end.



  Inductive Block : Type :=
     BlockJump : Label -> Instr -> Block
   | BlockJZ   : Var -> Label -> Label -> Block
   | BlockExit : Block.
  Hint Constructors Block.

  Variable Blocks : Label -> Block.
  Variable LabelPre  : Label -> Pred.

  Definition BlockPre (l : Label) (b : Block) : Prop :=
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
      : EvalI s (IInc v) (varUpdate v (S (s v)) s)
   | EvalIDec v s
      : EvalI s (IDec v) (varUpdate v (pred (s v)) s)
   | EvalINop s
      : EvalI s INop s.
  Hint Constructors EvalI.

  Inductive EvalB : Heap -> Label -> Heap -> Label -> Prop :=
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

  Theorem EvalI_Hoare i s s' post
   (hPre : InstrPre i post s)
   (hEvI : EvalI s i s')
         : post s'.
  Proof.
   !induction hEvI.
  Qed.

  Theorem BlockPre_Get l b
   (hBlock : Blocks l = b)
           : BlockPre l b.
  Proof.
    !rewrite <- hBlock.
  Qed.
  Hint Immediate BlockPre_Get.

  Theorem EvalB_Hoare l l' s s'
   (hPre : LabelPre l s)
   (hEvB : EvalB s l s' l')
         : LabelPre l' s'.
  Proof.
   !induction hEvB; destructs (BlockPre_Get H).
   !eapply EvalI_Hoare.
  Qed.



  Inductive EvalBs : Heap -> Label -> Heap -> Label -> Prop :=
   | EvalBs0 l s
      : Blocks l = BlockExit
     -> EvalBs s l s l
   | EvalBs1 l s l' s' l'' s''
      : EvalB  s l s' l'
     -> EvalBs s' l' s'' l''
     -> EvalBs s l s'' l''.


  Theorem EvalBs_Hoare l l' s s'
   (hPre : LabelPre l s)
   (hEvB : EvalBs s l s' l')
         : LabelPre l' s'.
  Proof.
   hint EvalB_Hoare.
   !induction hEvB.
  Qed.
End Goto.

Section Functor.
  Definition Instr_map_V {A B : Set} (f : A -> B) (i : Instr A) : Instr B :=
   match i with
   | IInc v => IInc (f v)
   | IDec v => IDec (f v)
   | INop _ => INop _
   end.

  Theorem Instr_map_V_id:
    forall A i, @Instr_map_V A A id i = i.
  Proof.
   !destruct i.
  Qed.

  Definition Block_map_V {L A B : Set} (f : A -> B) (b : Block A L) : Block B L :=
   match b with
   | BlockJump l i    => BlockJump l (Instr_map_V f i)
   | BlockJZ v lz lnz => BlockJZ (f v) lz lnz
   | BlockExit _ _    => BlockExit _ _
   end.
  Definition Block_map_L {V A B : Set} (f : A -> B) (b : Block V A) : Block V B :=
   match b with
   | BlockJump l i    => BlockJump (f l) i
   | BlockJZ v lz lnz => BlockJZ v (f lz) (f lnz)
   | BlockExit _ _    => BlockExit _ _
   end.

  Theorem Heap_comap_V {A B : Set} (f : B -> A) (h : Heap A) : Heap B.
    firstorder.
  Defined.

  Theorem Pred_map_V {A B : Set}
      (f : A -> B)
      (p : Pred A):
    Pred B.
  Proof.
   firstorder.
  Qed.
End Functor.
End Base.

Module Program.
 Module B := Base.

 Record Program (Var Label : Set) : Type
  := mkProgram
   { VarEqDec : EqDec Var
   ; Blocks   : Label -> B.Block Var Label
   ; LabelPre : Label -> B.Pred Var
   ; BlocksPre: (forall l : Label, B.BlockPre VarEqDec LabelPre l (Blocks l))
   }.

 Theorem LabelPre_rewrite V L (P : Program V L) l H H' :
    LabelPre P l H
  -> H' = H
  -> LabelPre P l H'.
 Proof. !intros; subst. Qed.


  Ltac Program_Block_destruct p l :=
    let pre := fresh "block_pre" in
    let eq  := fresh "block_eq" in
    destruct (Blocks p l) eqn:eq;
    lets pre: (BlocksPre p l);
    simpl;
    rewrite eq in *.

End Program.


Module Nowt.
  Inductive V0 : Set :=.
  Inductive L := L1.

  Definition LabelPre (l : L) (h : Base.Heap V0) := True.

  Module P := Program.
  Program Definition r := {| P.Blocks := (fun _ => Base.BlockExit V0 L); P.LabelPre := LabelPre |}.
  Next Obligation.
    decides_equality.
  Defined.
End Nowt.


Module Zero.
  Inductive V : Set := V1.
  Inductive L := L0 | L1 | L2.

  Module B := Base.
  Definition Blocks (l : L) :=
   match l with
   | L0 => B.BlockJump L1 (B.IDec V1)
   | L1 => B.BlockJZ V1 L2 L0
   | L2 => B.BlockExit V L
   end.
  Definition LabelPre (l : L) : B.Pred V :=
   match l with
   | L0 => fun h => True
   | L1 => fun h => True
   | L2 => fun h => h V1 = 0
   end.

  Program Definition r := {| Program.Blocks := Blocks; Program.LabelPre := LabelPre |}.
  Next Obligation.
    decides_equality.
  Defined.
  Next Obligation.
   destruct l; firstorder.
  Qed.
End Zero.

Module Seq.
 Module P := Program.
 Section Seq.
  Variable V L1 L2 : Set.
  Variable P1 : P.Program V L1.
  Variable P2 : P.Program V L2.
  Inductive L' := L'1 (l : L1) | L'2 (l : L2).

  Variable L2Start : L2.

  Hypothesis L2Pre:
    forall (l : L1),
    P.Blocks P1 l = Base.BlockExit _ _ ->
    (forall (h : Base.Heap V), (P.LabelPre P1 l h) -> (P.LabelPre P2 L2Start h)).

  Let Jumpy
   := Base.BlockJump (L'2 L2Start) (Base.INop V).

  Definition Blocks (l : L') :=
   match l with
   | L'1 l1
   => match P.Blocks P1 l1 with
      | Base.BlockExit _ _ => Jumpy
      | b => Base.Block_map_L (L'1) b
      end
   | L'2 l2 => Base.Block_map_L (L'2) (P.Blocks P2 l2)
   end.

  Definition LabelPre (l : L') :=
   match l with
   | L'1 l1 => P.LabelPre P1 l1
   | L'2 l2 => P.LabelPre P2 l2
   end.

  Program Definition r := {| P.VarEqDec := P.VarEqDec P1; P.Blocks := Blocks; P.LabelPre := LabelPre |}.
  Next Obligation.
    hint EqDec_Eq.

    !destruct l.
      !P.Program_Block_destruct P1 l.
        !unfold Jumpy; simpls.
      !P.Program_Block_destruct P2 l.
        !cuts_rewrite (P.VarEqDec P1 = P.VarEqDec P2).
   Qed.

 End Seq.
End Seq.



Module Alt.
 Module P := Program.
 Section Alt.
  Variable V1 V2 L1 L2 : Set.
  Variable P1 : P.Program V1 L1.
  Variable P2 : P.Program V2 L2.
  Inductive L' :=
    | L'1 (l1 : L1) (l2 : L2)
    | L'2 (l1 : L1) (l2 : L2).
  Inductive V' := V'1 (v : V1) | V'2 (v : V2).

  Definition Blocks (l : L') :=
   match l with
   | L'1 l1 l2
   => Base.Block_map_L (fun l1' => L'2 l1' l2)
     (Base.Block_map_V (V'1)
       (P.Blocks P1 l1))

   | L'2 l1 l2
   => Base.Block_map_L (fun l2' => L'1 l1 l2')
     (Base.Block_map_V (V'2)
       (P.Blocks P2 l2))
   end.

  Definition PredAnd (p1 : Base.Pred V1) (p2 : Base.Pred V2) : Base.Pred V' :=
   fun (h : Base.Heap V')
   => p1 (fun v1 => h (V'1 v1))
   /\ p2 (fun v2 => h (V'2 v2)).

  Definition LabelPreAnd (l1 : L1) (l2 : L2) : Base.Pred V' :=
    PredAnd (P.LabelPre P1 l1) (P.LabelPre P2 l2).

  Definition LabelPre (l : L') :=
   match l with
   | L'1 l1 l2 => LabelPreAnd l1 l2
   | L'2 l1 l2 => LabelPreAnd l1 l2
   end.

  Definition Heapjoin (h1 : Base.Heap V1) (h2 : Base.Heap V2) (v : V') :=
   match v with
   | V'1 v1 => h1 v1
   | V'2 v2 => h2 v2
   end.

  Theorem LabelPre__LabelPre l1 l2 h1 h2:
     P.LabelPre P1 l1 h1
  -> P.LabelPre P2 l2 h2
  -> PredAnd (P.LabelPre P1 l1) (P.LabelPre P2 l2) (Heapjoin h1 h2).
  Proof.
   firstorder.
  Qed.
  Print LabelPre__LabelPre.

  Program Definition r := {| P.Blocks := Blocks; P.LabelPre := LabelPre |}.
  Next Obligation.
    remember (P.VarEqDec P1).
    remember (P.VarEqDec P2).
    decides_equality.
  Qed.
  Next Obligation.
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
End Alt.
End Alt.



(*

Module Plus2.
  Module Var <: Var.
    Inductive Var' := VIn1 | VIn2 | VOut.
    Definition Var := Var'.
    Definition VarEqDec : EqDec Var.
    Proof. prove_eqdec. Qed.
    Definition update t := Map.update Var t VarEqDec.
  End Var.

  Module Label <: Label.
    Inductive Var' := VIn1 | VIn2 | VOut.
    Definition Var := Var'.
    Definition VarEqDec : EqDec Var.
    Proof. prove_eqdec. Qed.
    Definition update t := Map.update Var t VarEqDec.
*)