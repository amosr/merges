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
  Definition Pred := list Value -> list Value -> list Value -> Prop.

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
  Variable LabelPre  : Label -> list Label -> Pred.


  Inductive EvalB : list Value -> list Value -> list Value -> Label
                 -> list Value -> list Value -> list Value -> Label -> Prop :=
   | EvalBPullOk l lok lno i iss isr os
      : Blocks l = BlockPull lok lno
     -> EvalB iss (i::isr) os l
              (iss++[i]) isr  os lok

   | EvalBPullNo l lok lno iss os
      : Blocks l = BlockPull lok lno
     -> EvalB iss [] os l
              iss [] os lno


   | EvalBPush l push l' iss isr os
      : Blocks l = BlockPush push l'
     -> EvalB iss isr os l
              iss isr (os ++ [push]) l'

   | EvalBJump l l' iss isr os
      : Blocks l = BlockJump l'
     -> EvalB iss isr os l
              iss isr os l'
   .

  Variable Init : Label.
  Variable InitPre : forall isr, LabelPre Init [] [] isr [].

  Inductive EvalBs : list Value -> list Value -> list Value -> Label -> list Label -> Prop :=
   | EvalBs0 isr
      : EvalBs [] isr [] Init []
   | EvalBs1 l ls l' iss iss' isr isr' os os'
      : EvalBs iss isr os l ls
     -> EvalB  iss isr os l iss' isr' os' l'
     -> EvalBs iss' isr' os' l' (l::ls)
   | EvalBsNowt l ls iss isr os
      : EvalBs iss isr os l ls
     -> EvalBs iss isr os l (l::ls).

  Definition BlocksPreT :=
    forall iss iss' isr isr' os os' l ls l',
    EvalBs iss isr os l ls ->
    LabelPre l ls iss isr os ->
    EvalB  iss isr os l iss' isr' os' l' ->
    LabelPre l' (l::ls) iss' isr' os'.

  Hypothesis BlocksPre: BlocksPreT.

  Definition BlocksNowtT :=
    forall iss isr os l ls,
    LabelPre l     ls  iss isr os ->
    LabelPre l (l::ls) iss isr os.

  Hypothesis BlocksNowt: BlocksNowtT.

  Theorem EvalB_Step l iss isr os
   (hNotExit : Blocks l <> BlockExit)
         : exists l' iss' isr' os'
         , EvalB iss  isr  os  l
                 iss' isr' os' l'.
  Proof.
   Ltac CTOR C := !repeat eexists; eapply C.

   destruct (Blocks l) eqn:eql; tryfalse.
    destruct isr.
      CTOR EvalBPullNo.
      CTOR EvalBPullOk.
    CTOR EvalBPush.
    CTOR EvalBJump.
  Qed.


  Theorem EvalBs_Hoare l ls iss isr os
   (hEvB : EvalBs iss  isr  os l ls)
         : LabelPre l ls iss isr os.
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
   ; LabelPre : Label -> list Label -> B.Pred
   ; BlocksPre: B.BlocksPreT Blocks LabelPre Init
   ; InitPre  : forall is, LabelPre Init [] [] is []
   ; BlocksNowt : B.BlocksNowtT LabelPre
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

Module ProgramConst.
  Module B := Base.

  Inductive L := L0 | L1 | L2.

  Definition Blocks (l : L) : B.Block L :=
   match l with
   | L0 => B.BlockPull L1 L2
   | L1 => B.BlockPush 0 L0
   | L2 => B.BlockExit L
   end.
  Definition LabelPre (l : L) (ls : list L) : B.Pred :=
   match l with
   | L0 => fun iss isr os => map (fun _ => 0) iss = os
   | L1 => fun iss isr os => map (fun _ => 0) iss = os ++ [0]
   | L2 => fun iss isr os => isr = [] /\ map (fun _ => 0) iss = os
   end.


  Program Definition r := {| Program.Blocks := Blocks; Program.LabelPre := LabelPre; Program.Init := L0 |}.
  Next Obligation.
   introv hEvBs hLbl hEvB.
   !destruct l; inverts hEvB; tryfalse; simpls; inject_all; simpls.
   !rewrite map_app; subst.
  Qed.
  Next Obligation.
   introv hLbl.
   !destruct l.
  Qed.
End ProgramConst.

Module ProgramEvenIxs.
  Module B := Base.

  Fixpoint evenIxs (l : list nat) : list nat :=
  match l with
   | x :: y :: l' => 0 :: evenIxs l'
   | [x] => [0]
   | []  => []
  end.

  Inductive L := L'Pull1 | L'Push1 | L'Pull2 | L'End.

  Definition Blocks (l : L) : B.Block L :=
   match l with
   | L'Pull1 => B.BlockPull L'Push1 L'End
   | L'Push1 => B.BlockPush 0 L'Pull2
   | L'Pull2 => B.BlockPull L'Pull1 L'End
   | L'End   => B.BlockExit L
   end.

  Inductive Even : nat -> Prop :=
  | Even0 : Even 0
  | EvenSS n : Even n -> Even (S (S n)).
  Hint Constructors Even.

  Theorem app_evenIxs (a b : list nat)
    (hEven : Even (length a)):
    evenIxs (a ++ b) = evenIxs a ++ evenIxs b.
  Proof.
   remember (length a).
   gen a.
   !induction hEven; intros; destruct a; tryfalse.

   destruct a; tryfalse.
   simpl. !rewrite IHhEven. simpls. congruence.
  Qed.

  Theorem app_evenIxs_odd (a b : list nat)
    (hEven : Even (S (length a))):
    evenIxs (a ++ b) = evenIxs a ++ evenIxs (tail b).
  Proof.
   remember (S (length a)).
   gen a.
   !induction hEven; intros;
    destruct a; tryfalse.
   destruct a; tryfalse.
   simpls.
    !destruct b.
   simpls.
    !rewrite IHhEven. congruence.
  Qed.

  Definition LabelPre (l : L) (ls : list L) : B.Pred :=
   match l with
   | L'Pull1 => fun iss isr os => Even (length iss) /\ os = evenIxs iss
   | L'Push1 => fun iss isr os => Even (S (length iss)) /\ os ++ [0] = evenIxs iss
   | L'Pull2 => fun iss isr os => Even (S (length iss)) /\ os = evenIxs iss
   | L'End   => fun iss isr os => isr = [] /\ os = evenIxs iss
   end.

  Program Definition r := {| Program.Blocks := Blocks; Program.LabelPre := LabelPre; Program.Init := L'Pull1 |}.
  Next Obligation.
   introv hEvBs hLbl hEvB.
   !destruct l; inverts hEvB; tryfalse; simpls; inject_all; simpls;
    try rewrite app_length;
    simpl; try rewrite Nat.add_1_r;
    destructs hLbl.
    !try rewrite app_evenIxs; subst.

    !rewrite app_evenIxs_odd; subst; simpls.
    !rewrite app_nil_r.
  Qed.
  Next Obligation.
   introv hLbl.
   !destruct l.
  Qed.
End ProgramEvenIxs.


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

  Definition L1ofL' (l : L') :=
  match l with
  | LX l1 l2 _ _ => l1
  end.
  Definition L2ofL' (l : L') :=
  match l with
  | LX l1 l2 _ _ => l2
  end.

  Definition LabelPre (l : L') (ls : list L') : B.Pred :=
   match l with
   | LX l1 l2 _ _
   => fun iss isr os
   => exists iss' isr',
      P.EvalBs P1 iss  isr (iss'++isr') l1 (map L1ofL' ls)
   /\ P.EvalBs P2 iss' isr' os l2 (map L2ofL' ls)
   (*/\ P.LabelPre P1 l1 (map L1ofL' ls) iss  isr  (iss' ++ isr')
   /\ P.LabelPre P2 l2 (map L2ofL' ls) iss' isr' os *)
   end.
  Hint Unfold LabelPre.


  Program Definition r := {| P.Blocks := Blocks; P.LabelPre := LabelPre; P.Init := LX (P.Init P1) (P.Init P2) Ok Ok |}.
  Next Obligation.
   unfolds B.BlocksPreT.
   introv hEvBs hLbl hEvB.
   destruct l; destruct l'.
   !inverts hEvB; simpls;
    destruct (P.Blocks P1 l1) eqn:P1Block;
    destruct (P.Blocks P2 l2) eqn:P2Block;
    destruct s1; destruct s2;

    inject_all; simpls; tryfalse; jauto_set
  ; try solve [!eapply B.EvalBsNowt]
  ; try solve [!destruct (P.Blocks P2 l2) eqn:P2Block; tryfalse; destruct s1; destruct s2; tryfalse]
  ; try solve [!destruct (P.Blocks P2 l2) eqn:P2Block; tryfalse; destruct s1; destruct s2; tryfalse; inject_all; eapply B.EvalBsNowt]
  ; try solve [(!eapply B.EvalBs1); !eapply B.EvalBPullOk]
  ; try solve [(!eapply B.EvalBs1); !eapply B.EvalBPullNo]
  ; try solve [(!eapply B.EvalBs1); !eapply B.EvalBPush]
  ; try solve [(!eapply B.EvalBs1); !eapply B.EvalBJump]
  .

  !eapply B.EvalBs1.
   !applys_eq B.EvalBPullOk 0.
   !fequals.
   !applys B.EvalBPullOk 0.
  !eapply B.EvalBs1. !eapply B.EvalBPullNo.

  !destruct (P.Blocks P2 l2) eqn:P2Block; tryfalse; destruct s1; destruct s2; tryfalse;
  inject_all;
  (!eapply B.EvalBs1); !eapply B.EvalBPush.

  !destruct (P.Blocks P2 l2) eqn:P2Block; tryfalse; destruct s1; destruct s2; tryfalse;
  inject_all;
  (!eapply B.EvalBs1); !eapply B.EvalBPush.

  !destruct (P.Blocks P2 l2) eqn:P2Block; tryfalse; destruct s1; destruct s2; tryfalse;
  inject_all;
  try solve [(!eapply B.EvalBs1); !eapply B.EvalBPush]
  .
  (!eapply B.EvalBs1); !eapply B.EvalBPush.
  eapply B.EvalBsNowt.
  (!eapply B.EvalBs1); !eapply B.EvalBPush.

  !eapply B.EvalBsNowt. apply H0.
  (!eapply B.EvalBs1); !eapply B.EvalBPush.


    destruct (P.Blocks P2 l2) eqn:P2Block; tryfalse;
    !destruct s1; destruct s2; tryfalse.


  unfolds.

  !eapply BlocksPreP1.
    !inverts H. !destruct ls; simpls; tryfalse.
      apply P.InitPre.


   lets BlocksPreP1: P.BlocksPre P1.
   lets BlocksPreP2: P.BlocksPre P2.

    
   split.
   inverts H; try inverts H8; tryfalse.
    assert (iss0 = iss /\ i0 = i).
      gen H. clear. gen iss.
      !induction iss0; intros; destruct iss; simpls; subst; inverts H.
      destruct iss; tryfalse.
      destruct iss0; tryfalse.
      !destruct (IHiss0 iss); subst.
    jauto_set; subst.
   !apply (BlocksPreP1 ) with (iss := iss) (isr := i :: isr') (os := iss' ++ isr'0).
   !apply hLbl.
    !inverts hEvBs.
    unfold P.EvalBs.


apply B.EvalBsNowt.
   (* almost, but need to remove repeats from evaluation
    or add an EvalBs rule for staying on same place *)


 inverts H0. !inverts H10.
  

  inject_all. inverts H1. tryfalse.
    SearchRewrite (_ ++ [_]).

   !apply (BlocksPreP1 ) with (iss := iss) (isr := i :: isr') (os := iss' ++ isr'0).

iss _ (i :: isr') _ (iss' ++ isr'0)
   

   destruct (P.Blocks P2 l2) eqn:P2Block.
    simpls.
   inverts hEvB. tryfalse; simpls; inject_all; simpls.

   introv hEvBs.
   gen iss' isr' os' l'.
   !induction hEvBs; introv hLbl hEvB.
    !inverts hEvB; simpls;
      destruct (P.Blocks P1 (P.Init P1)) eqn:BlockP1;
      inject_all;
      tryfalse;
      simpls; intros.

    !splits.
    !eapply (BlocksPreP1 []).
      apply B.EvalBs0. !apply (P.InitPre P1).
      !auto.

    simpls.
    simpls. inverts hEvB; tryfalse. simpls.
    simpls.
    simpls; inverts hEvB.
    simpls; subst.
    simpls.
    
   !destruct l; inverts hEvB; tryfalse; simpls; inject_all; simpls;

   destruct l.
    P.Program_Block_destruct P1 l1.
     + simpls; splits; intros; destructs block_pre.
      - !destruct (H0 iss' isr'); split.
          apply H1.
         apply
         inverts H0.
          destruct iss; tryfalse.
         
         inverts H5.
          apply app_inj_tail in H0; destructs H0.
          applys_eq H4 0.
          unfolds. fequals.
            rewrite <- app_assoc. simpl. auto.
          assert 

apply_with_vengeance H2.
        destruct (H iss' isr').
        unfold P.EvalFromInit.
        inverts H0. destruct iss; tryfalse.
        applys_eq H4 0. fequals.
          !rewrite <- app_assoc.
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