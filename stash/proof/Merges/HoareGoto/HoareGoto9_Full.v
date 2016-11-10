(* Multiple inputs and outputs, blocking reads *)
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

  Variable ChanV : Set.
  Variable ChanVEqDec : EqDec ChanV.

  Variable ScalarV : Set.
  Variable ScalarVEqDec : EqDec ScalarV.

  Definition StreamHeap := Map ChanV (list Value).
  Definition ScalarHeap := Map ScalarV Value.
  Definition Pred := StreamHeap -> ScalarHeap -> Prop.

  Let streamUpdate := Map.update ChanV (list Value) ChanVEqDec.
  Let scalarUpdate := Map.update ScalarV Value ScalarVEqDec.

  Inductive StreamTypeT :=
   | Input | Output | Ignore.
  Variable StreamType : ChanV -> StreamTypeT.

  Inductive Block : Type :=
   (* Blocking pull, wait forever until we get something *)
   | BlockPull : ScalarV -> ChanV -> Label -> Block
   (* Release the thing we just pulled.
      When two machines are pulling from same thing, this
      signals to other machine that it can now pull if it wants *)
   | BlockRelease : ChanV -> Label -> Block

   (* Push a value *)
   | BlockPush : ChanV -> (ScalarHeap -> Value) -> Label -> Block

   (* Update a variable *)
   | BlockUpdate : ScalarV -> (ScalarHeap -> Value) -> Label -> Block

   (* If non-zero *)
   | BlockIf : (ScalarHeap -> Value) -> Label -> Label -> Block

   (* Jump to another label without doing anything *)
   | BlockJump   : Label -> Block
   .

  Variable Blocks : Label -> Block.
  Variable LabelPre  : Label -> Pred.

  Inductive EvalB : StreamHeap -> ScalarHeap -> Label
                 -> StreamHeap -> ScalarHeap -> Label -> Prop :=
   | EvalBPullOk l v c lok i h sh
      : Blocks l = BlockPull v c lok
     -> StreamType c = Input
     -> EvalB h sh l
              (streamUpdate c (i :: h c) h) (scalarUpdate v i sh) lok

   (* Release does nothing *)
   | EvalBRelease l v l' h sh
      : Blocks l = BlockRelease v l'
     -> StreamType v = Input
     -> EvalB h sh l
              h sh l'

   | EvalBPush l v push l' h sh
      : Blocks l = BlockPush v push l'
     -> StreamType v = Output
     -> EvalB h sh l
              (streamUpdate v (push sh :: h v) h) sh l'

   | EvalBUpdate l v f l' h sh
      : Blocks l = BlockUpdate v f l'
     -> EvalB h sh l
              h (scalarUpdate v (f sh) sh) l'

   | EvalBIfZ l f lz lnz h sh
      : Blocks l = BlockIf f lz lnz
     -> f sh = 0
     -> EvalB h sh l
              h sh lz

   | EvalBIfS l f lz lnz h sh n
      : Blocks l = BlockIf f lz lnz
     -> f sh = S n
     -> EvalB h sh l
              h sh lnz

   | EvalBJump l l' h sh
      : Blocks l = BlockJump l'
     -> EvalB h sh l
              h sh l'

   | EvalBIgnore l v i h sh
      : StreamType v = Ignore
     -> EvalB h sh l
              (streamUpdate v (i :: h v) h) sh l
   .
  Hint Constructors EvalB.

  Variable Init : Label.
  Variable InitPre : LabelPre Init (fun _ => []) (fun _ => 0).

  Inductive EvalBs : StreamHeap -> ScalarHeap -> Label -> Prop :=
   | EvalBs0
      : EvalBs (fun _ => []) (fun _ => 0) Init
   | EvalBs1 l l' h h' sh sh'
      : EvalBs h sh l
     -> EvalB  h sh l h' sh' l'
     -> EvalBs h' sh' l'
   .
  Hint Constructors EvalBs.

  Definition BlocksPreT :=
    forall h h' sh sh' l l',
    EvalBs h sh l ->
    LabelPre l h sh ->
    EvalB  h sh l h' sh' l' ->
    LabelPre l' h' sh'.

  Hypothesis BlocksPre: BlocksPreT.

  Theorem EvalBs_Hoare l h sh
   (hEvB : EvalBs h sh l)
         : LabelPre l h sh.
  Proof.
   !induction hEvB.
  Qed.
End Machine.

End Base.


  Ltac destruct_apps FUN :=
  repeat match goal with
  | [ _ : context [ FUN ?a ] |- _ ]
  => let x := fresh "destruct_" FUN in remember (FUN a) as x
     ; destruct x
     ; tryfalse
     ; repeat match goal with
       | [ H : _ = FUN a |- _ ] => gen H
       end
  end;
   intros.

  Ltac matchmaker Heq :=
   match goal with
  | [ Heq : _ = match ?A with | _ => _ end |- _ ]
  => let x    := fresh "scrut_" Heq
  in let Heqx := fresh "Heq_" x
  in remember A as x eqn:Heqx; destruct x; try rewrite <- Heqx in *; tryfalse
   ; try matchmaker Heqx
  | [ Heq : match ?A with | _ => _ end = _ |- _ ]
  => let x    := fresh "scrut_" Heq
  in let Heqx := fresh "Heq_" x
  in remember A as x eqn:Heqx; destruct x; try rewrite <- Heqx in *; tryfalse
   ; try matchmaker Heqx
  end.


  Ltac matchmaker_goal := repeat
   match goal with
  | [ |- context [match ?A with | _ => _ end] ]
  => let x    := fresh "scrut_"
  in let Heqx := fresh "Heq_" x
  in remember A as x eqn:Heqx; destruct x; substs; try rewrite <- Heqx in *; tryfalse
   ; try matchmaker Heqx
  end.

 Ltac matchmaker_goal' :=
            !repeat
           match goal with
          | [ |- context [match ?A with | _ => _ end] ]
          => let x    := fresh "scrut_"
          in let Heqx := fresh "Heq_" x
          in remember A as x eqn:Heqx; destruct x
           ; try matchmaker Heqx
           ; try rewrite <- Heqx in *; tryfalse
          end.



Module Program.
 Module B := Base.

 Record Program (Label : Set) (ChanVar : Set) (ScalarVar : Set) : Type
  := mkProgram
   { Init     : Label
   ; Blocks   : Label -> B.Block Label ChanVar ScalarVar

   ; ChanVarEqDec : EqDec ChanVar
   ; ScalarVarEqDec : EqDec ScalarVar
   ; StreamType : ChanVar -> B.StreamTypeT

   ; LabelPre : Label -> B.Pred ChanVar ScalarVar
   ; BlocksPre: B.BlocksPreT ChanVarEqDec ScalarVarEqDec StreamType Blocks LabelPre Init
   ; InitPre  : LabelPre Init (fun _ => []) (fun _ => 0)
   }.

  Definition EvalBs (Label : Set) (ChanVar : Set) (ScalarVar : Set) (P : Program Label ChanVar ScalarVar)
   := B.EvalBs (ChanVarEqDec P) (ScalarVarEqDec P) (StreamType P) (Blocks P) (Init P).

End Program.


Module Fuse.
  Module B := Base.
  Module P := Program.

Section Fuse.
  Variable C : Set.
  Variable V1 : Set.
  Variable L1 : Set.
  Variable P1 : P.Program L1 C V1.

  Variable V2 : Set.
  Variable L2 : Set.
  Variable P2 : P.Program L2 C V2.

  Variable EqDec_C : EqDec C.

  Inductive V :=
    | V'V1 : V1 -> V
    | V'V2 : V2 -> V
    | V'C : C -> V.

  (* Figure out what the fused StreamType will be *)
  Definition StreamType (c : C) : B.StreamTypeT :=
  match P.StreamType P1 c, P.StreamType P2 c with
  (* If left ignores, take whatever right does *)
  | B.Ignore, t
  => t
  (* Vice versa *)
  | t, B.Ignore
  => t
  (* If either is an output, it will be an output in the fused *)
  | B.Output, _
  => B.Output
  | _, B.Output
  => B.Output
  (* If both are inputs, end result is an input *)
  | B.Input, B.Input
  => B.Input
  end.

  Inductive State :=
    | NoValue         (* Input, Output, Ignore *)
    | AvailableToPull (* Input *)
    | HaveValue       (* Input *)
    | ReadyToPush     (* Output *)
    .

  Inductive IsValid :=
    | Valid
    | INVALID
    .

  Inductive L' :=
    | LX (l1 : L1) (l2 : L2) (s1 : C -> State) (s2 : C -> State) (v : IsValid).

  Definition stateUpdate := Map.update C State (P.ChanVarEqDec P1).

  Inductive BlockOption :=
    | BlockOk (b : B.Block L' C V)
    | BlockTryOther
    | BlockINVALID
    .

  Definition makeBlock
    (LA VA : Set)
    (mkV : VA -> V)
    (mkLabel : LA -> (C -> State) -> (C -> State) -> L')
    (lblThis : LA)
    (block : B.Block LA C VA)
    (sThis sOther : C -> State)
    (typeThis : C -> B.StreamTypeT)
    (typeOther : C -> B.StreamTypeT)
           : BlockOption :=
   match block with
    (* Jumps are very easy *)
    | B.BlockJump _ _ l'
    => BlockOk (B.BlockJump _ _ (mkLabel l' sThis sOther))

    (* Releases are fairly simple, so let's start with them *)
    | B.BlockRelease _ sv l'
    => match typeThis sv, typeOther sv, sThis sv, sOther sv with
       (* If the other machine ignores this, we can just release with no synchronisation *)
       (* We require sThis and sOther to be 'NoValue' even though there is something: *)
       (* it doesn't need to be tracked because it's ignored *)
       | B.Input, B.Ignore, NoValue, NoValue
       => BlockOk (B.BlockRelease _ sv (mkLabel l' sThis sOther))

       (* Both machines want to pull from this, so let's see.
          This machine must have a value for sv in its state now:
          sThis sv = HaveValue
          But it depends whether the other machine has it
       *)
       | B.Input, B.Input, HaveValue, HaveValue
       | B.Input, B.Input, HaveValue, AvailableToPull
       (* If other machine still has one, we only pretend to release *)
       => BlockOk (B.BlockJump _ _ (mkLabel l' (stateUpdate sv NoValue sThis) sOther))

       (* Other machine has already pretended to release *)
       | B.Input, B.Input, HaveValue, NoValue
       => BlockOk (B.BlockRelease _ sv (mkLabel l' (stateUpdate sv NoValue sThis) sOther))

       (* The other machine has already pushed this, so only pretend release *)
       (* sOther = NoValue because the push has already happened *)
       | B.Input, B.Output, HaveValue, NoValue
       => BlockOk (B.BlockJump _ _ (mkLabel l' (stateUpdate sv NoValue sThis) sOther))

       (* Otherwise sThis sv is invalid *)
       | _, _, _, _
       => BlockINVALID
       end

    (* Pulls are a bit more interesting *)
    | B.BlockPull v c l'
    => match typeThis c, typeOther c, sThis c, sOther c with
       (* Ignore is easy *)
       | B.Input, B.Ignore, NoValue, NoValue
       => BlockOk (B.BlockPull (mkV v) c (mkLabel l' sThis sOther))

       (* Both machines want to pull from this, so let's see. *)
       (* We already have a fake one ready to go, so use it *)
       | B.Input, B.Input, AvailableToPull, NoValue
       | B.Input, B.Input, AvailableToPull, HaveValue
       | B.Input, B.Input, AvailableToPull, AvailableToPull
       => BlockOk (B.BlockUpdate _
                    (mkV v) (fun sh => sh (V'C c))
                    (mkLabel l' (stateUpdate c HaveValue sThis) sOther))

       | B.Input, B.Input, NoValue, HaveValue
       | B.Input, B.Input, NoValue, AvailableToPull
       (* If other machine has one but we don't, that means
          we have already pulled and released, but they haven't released yet.
          They need to run a bit and hopefully release.
        *)
       => BlockTryOther

       | B.Input, B.Input, NoValue, NoValue
       (* Neither machine has it, but we both want it.
          Both now have the value available and the next step will use it *)
       => BlockOk (B.BlockPull (V'C c) c
                  (mkLabel lblThis
                      (stateUpdate c AvailableToPull sThis)
                      (stateUpdate c AvailableToPull sOther)))

       (* The other machine must push. Have they given us anything yet? *)
       (* Yes, they have given us something *)
       | B.Input, B.Output, AvailableToPull, NoValue
       => BlockOk (B.BlockUpdate _ (mkV v) (fun sh => sh (V'C c)) (mkLabel l'  (stateUpdate c HaveValue sThis) sOther))

       (* No, we have to wait. Try to let the other machine run *)
       | B.Input, B.Output, NoValue, NoValue
       | B.Input, B.Output, NoValue, ReadyToPush
       => BlockTryOther

       (* Otherwise sThis sv is invalid *)
       | _, _, _, _
       => BlockINVALID
       end

    (* Pushes are pretty similar *)
    | B.BlockPush sv f l'
    => match typeThis sv, typeOther sv, sThis sv, sOther sv with
       (* It's pretty easy if the other machine ignores this channel *)
       | B.Output, B.Ignore, NoValue, NoValue
       => BlockOk (B.BlockPush sv (fun sh => f (fun v => sh (mkV v))) (mkLabel l' sThis sOther))

       (* Other machine reads: *)
       (* Check if it is ready to scoop a new one *)
       | B.Output, B.Input, NoValue, HaveValue
       | B.Output, B.Input, NoValue, AvailableToPull
       (* No. The other machine has a value it hasn't already used *)
       => BlockTryOther

       (* Other machine is empty and ready to receive.
          Save the output value to the local V'C buffer so the pull can use it
           And next step will do the actual push *)
       | B.Output, B.Input, NoValue, NoValue
       => BlockOk
         (B.BlockUpdate _ (V'C sv)
             (fun sh => f (fun v => sh (mkV v)))
             (mkLabel lblThis (stateUpdate sv ReadyToPush sThis) sOther))

       (* We have already saved the output in V'C *)
       | B.Output, B.Input, ReadyToPush, NoValue
       => BlockOk
          (B.BlockPush sv
            (fun sh => sh (V'C sv))
            (mkLabel l' (stateUpdate sv NoValue sThis) (stateUpdate sv AvailableToPull sOther)))

       (* All other cases are invalid *)
       | _, _, _, _
       => BlockINVALID
       end
    | B.BlockUpdate _ v f l'
    => BlockOk (B.BlockUpdate _ (mkV v) (fun sh => f (fun v => sh (mkV v))) (mkLabel l' sThis sOther))
    | B.BlockIf _ f lz lnz
    => BlockOk (B.BlockIf _ (fun sh => f (fun v => sh (mkV v)))
                    (mkLabel lz sThis sOther)
                    (mkLabel lnz sThis sOther)
                )
   end.


  Definition Blocks (l : L') : B.Block L' C V :=
   match l with
   | LX l1 l2 s1 s2 v
   => let invalid := B.BlockJump _ _ (LX l1 l2 s1 s2 INVALID) in
      match v
    , makeBlock V'V1 (fun l1' s1' s2' => LX l1' l2 s1' s2' Valid) l1 (P.Blocks P1 l1) s1 s2 (P.StreamType P1) (P.StreamType P2)
    , makeBlock V'V2 (fun l2' s2' s1' => LX l1 l2' s1' s2' Valid) l2 (P.Blocks P2 l2) s2 s1 (P.StreamType P2) (P.StreamType P1)
      with
      | Valid, BlockINVALID, _
      => invalid
      | Valid, _, BlockINVALID
      => invalid
      | Valid, BlockOk block, _
      => block
      | Valid, _, BlockOk block
      => block
      | _, _, _
      => invalid
      end
    end.

  Definition Evalish (LA VA : Set) (mkV : VA -> V) (P : P.Program LA C VA) (s : C -> State) (iss : B.StreamHeap C) (h : B.ScalarHeap V) (l : LA) : Prop :=
   let iss' :=
    fun sv =>
     match s sv with
      | AvailableToPull => tail (iss sv)
      | HaveValue       => iss sv
      | NoValue         => iss sv
      | ReadyToPush     => iss sv
     end
   in P.EvalBs P iss' (fun v => h (mkV v)) l /\
    (forall sv,
     match s sv with
      | AvailableToPull
      => match iss sv with
         | [] => False
         | x :: _ => x = h (V'C sv)
         end
      | HaveValue => True
      | NoValue   => True
      | ReadyToPush
      => match P.Blocks P l with
         | B.BlockPush sv' f _
         => sv = sv' /\ h (V'C sv) = f (fun v => h (mkV v))
         | _ => False
         end
     end /\
     (P.StreamType P sv = B.Ignore -> s sv = NoValue)
     ).

  Definition LabelPre (l : L') : B.Pred C V :=
   match l with
   | LX l1 l2 s1 s2 INVALID
   => fun _ _ => True
   | LX l1 l2 s1 s2 Valid
   => fun iss h
   => Evalish V'V1 P1 s1 iss h l1
   /\ Evalish V'V2 P2 s2 iss h l2
   end.
  Hint Unfold LabelPre.

  Theorem ScalarVarEqDec_V: EqDec V.
  Proof.
    hint (P.ScalarVarEqDec P1).
    hint (P.ScalarVarEqDec P2).
    hint EqDec_C.
    decides_equality.
  Qed.

  Theorem ScalarHeap_update_sub
      (V' : Set)
      (Eq_V' : EqDec V')
      (mkV' : V' -> V)
      (mkV'inj : forall a b, mkV' a = mkV' b -> a = b) 
      (sh : B.ScalarHeap V)
      (i : B.Value) (v0 : V'):
  (fun v : V' => update V P.B.Value ScalarVarEqDec_V (mkV' v0) i sh (mkV' v)) =
    update V' B.Value Eq_V' v0 i (fun v : V' => sh (mkV' v)).
  Proof.
    extensionality n.
    unfolds.
    !destruct (ScalarVarEqDec_V); destruct (Eq_V').
    !destruct n0.
    !destruct n0. !rewrite e.
  Qed.
  Program Definition ScalarHeap_update_sub_V1
    := ScalarHeap_update_sub (P.ScalarVarEqDec P1) V'V1 _.
  Program Definition ScalarHeap_update_sub_V2
    := ScalarHeap_update_sub (P.ScalarVarEqDec P2) V'V2 _.

  Theorem ScalarHeap_update_V1_as_V2 i sh v0:
    (fun v : V2 => update V P.B.Value ScalarVarEqDec_V (V'V1 v0) i sh (V'V2 v)) =
    (fun v : V2 => sh (V'V2 v)).
  Proof.
    extensionality v.
    unfolds.
    !destruct ScalarVarEqDec_V.
    tryfalse.
  Qed.

  Theorem ScalarHeap_update_V2_as_V1 i sh v0:
    (fun v : V1 => update V P.B.Value ScalarVarEqDec_V (V'V2 v0) i sh (V'V1 v)) =
    (fun v : V1 => sh (V'V1 v)).
  Proof.
    extensionality v.
    unfolds.
    !destruct ScalarVarEqDec_V.
    tryfalse.
  Qed.

  Theorem ScalarHeap_update_VC_as_V1 i sh c0:
    (fun v : V1 => update V P.B.Value ScalarVarEqDec_V (V'C c0) i sh (V'V1 v)) =
    (fun v : V1 => sh (V'V1 v)).
  Proof.
    extensionality v.
    unfolds update.
    !destruct (ScalarVarEqDec_V); tryfalse.
  Qed.

  Theorem ScalarHeap_update_VC_as_V2 i sh c0:
    (fun v : V2 => update V P.B.Value ScalarVarEqDec_V (V'C c0) i sh (V'V2 v)) =
    (fun v : V2 => sh (V'V2 v)).
  Proof.
    extensionality v.
    unfolds update.
    !destruct (ScalarVarEqDec_V); tryfalse.
  Qed.


  Ltac doit X := try solve [(!eapply B.EvalBs1); (!eapply X)].

  Ltac rewrite_Heaps :=
      try rewrite ScalarHeap_update_sub_V1;
      try rewrite ScalarHeap_update_sub_V2;
      try rewrite ScalarHeap_update_V1_as_V2;
      try rewrite ScalarHeap_update_V2_as_V1;
      try rewrite ScalarHeap_update_VC_as_V2;
      try rewrite ScalarHeap_update_VC_as_V1.





  Program Definition r
  := {| P.Blocks := Blocks
      ; P.LabelPre := LabelPre
      ; P.Init := LX (P.Init P1) (P.Init P2) (fun _ => NoValue) (fun _ => NoValue) Valid
      ; P.StreamType := StreamType
      ; P.ChanVarEqDec := P.ChanVarEqDec P1
      ; P.ScalarVarEqDec := ScalarVarEqDec_V
      |}.

  Next Obligation.


   unfolds B.BlocksPreT.
   introv hEvBs hLbl hEvB.
   clear hEvBs.
   destruct l; destruct l'.
   !destruct v0; destruct v; try solve [inverts hEvB; tryfalse].

   simpls; unfolds Evalish; unfolds Blocks; unfolds makeBlock.

  inverts hEvB.
  - (* BlockPull *)

    matchmaker H.
    all: inject_all.
    all: rewrite_Heaps.
    all: !jauto_set.

    all: try solve [
      match goal with
      | [ |- context [P.EvalBs P1] ] => applys_eq H 0
      | [ |- context [P.EvalBs P2] ] => applys_eq H1 0
      end; fequals;
      extensionality sv;
      unfolds stateUpdate;
      unfolds update;
      !destruct (P.ChanVarEqDec);
      subst; simpl;
      !destruct (s1 sv); destruct (s2 sv); tryfalse ].

    all: try solve
      [
   (!eapply B.EvalBs1);
    (!applys_eq B.EvalBIgnore 0; fequals);
    extensionality n;
    unfolds update;
    (!repeat destruct P.ChanVarEqDec; subst; destruct (s1 n); destruct (s2 n); tryfalse)
      ].

    all: try solve
      [
   (!eapply B.EvalBs1);
    (!applys_eq B.EvalBPullOk 0; fequals);
    extensionality n;
    unfolds update;
    (!repeat destruct P.ChanVarEqDec; subst; destruct (s1 n); destruct (s2 n); tryfalse)
      ].

    all: intros sv; unfolds stateUpdate; forwards: H0 sv; forwards: H2 sv.

    all: unfolds update.
    all: matchmaker_goal'.
    all: !jauto_set.

    all: substs.
    all: !inject_all.
    all: intros; tryfalse.

  - (* BlockRelease *)
    matchmaker H.
    all: inject_all.
    all: !jauto_set.
    all: doit B.EvalBRelease
       ; try assumption
      .

    all: try solve
      [
   (!eapply B.EvalBs1);
    (!applys_eq B.EvalBRelease 0; fequals);
    extensionality n;
    unfolds stateUpdate; unfolds update;
    (!repeat destruct P.ChanVarEqDec; subst; destruct (s1 n); destruct (s2 n); tryfalse)
      ].

    all: intros sv.
    all: unfolds stateUpdate; unfolds update; forwards: H0 sv; forwards: H2 sv.

    all: matchmaker_goal'.
    all: !inject_all.
    all: !jauto_set.
    all: tryfalse.

  - (* BlockPush *)

    matchmaker H.
    all: inject_all.
    all: !jauto_set.

    all: try solve
      [
       (!eapply B.EvalBs1);
        (!applys_eq B.EvalBPush 0; fequals);
        extensionality n;
        unfolds stateUpdate; unfolds update;
        (!repeat destruct P.ChanVarEqDec; subst);
        forwards: H0 n; forwards: H2 n;
        (!destruct (s1 n); destruct (s2 n); tryfalse);
        (!jauto_set); congruence
      ].

    all: unfolds stateUpdate; unfolds update.

    all: try solve [
      match goal with
      | [ |- context [P.EvalBs P1] ] => applys_eq H 0
      | [ |- context [P.EvalBs P2] ] => applys_eq H1 0
      end; fequals;
      extensionality sv;
      unfolds stateUpdate;
      unfolds update;
      !destruct (P.ChanVarEqDec);
      subst; simpl;
      !destruct (s1 sv); destruct (s2 sv); tryfalse ].


    all: try solve [
      (!eapply B.EvalBs1);
      (!applys_eq B.EvalBIgnore 0; fequals);
      extensionality sv;
      unfolds update;
      (!repeat destruct P.ChanVarEqDec; tryfalse; subst);
      simpl;
      (!destruct (s1 sv); destruct (s2 sv); tryfalse)
      ].

    all: intros sv.
    all: !jauto_set.
    all: !forwards: H0 sv; forwards: H2 sv; jauto_set.


    all: matchmaker_goal'.
    all: !inject_all.
    all: substs.
    all: !jauto_set; tryfalse.

  - (* BlockUpdate *)
    !jauto_set.
    + (* EvalBs P1 *)
      matchmaker H.
      all: inject_all.


      all: rewrite_Heaps.

      all: try solve [
        (!eapply B.EvalBs1); (!applys_eq B.EvalBPullOk 2 3);
        extensionality sv;
        forwards: H1 sv;
        unfolds stateUpdate; unfolds update;
        jauto_set;
        matchmaker_goal;
        (!destruct (h' sv); tryfalse);
        (!simpl; subst)
        ].

      all: try solve [
        (!applys_eq H0 2 3);
        extensionality sv;
        forwards: H1 sv;
        unfolds stateUpdate; unfolds update;
        matchmaker_goal;
        (!destruct (h' sv); tryfalse);
        (!simpl; subst)
        ].

      all: try solve [
        (!eapply B.EvalBs1); (!applys_eq B.EvalBUpdate 2 3);
        extensionality sv;
        forwards: H1 sv;
        unfolds stateUpdate; unfolds update;
        matchmaker_goal;
        (!destruct (h' sv); tryfalse);
        (!simpl; subst)
        ].

    + (* P1 invariant *)
        intros sv.
        forwards: H1 sv.
        unfolds stateUpdate; unfolds update.
        matchmaker H; inject_all.


  all: !repeat
   match goal with
  | [ |- context [match ?A with | _ => _ end] ]
  => let x    := fresh "scrut_"
  in let Heqx := fresh "Heq_" x
  in remember A as x eqn:Heqx; destruct x
   ; try matchmaker Heqx
   ; try rewrite <- Heqx in *; tryfalse
  end.
  all: inject_all.
  all: !jauto_set.


    all: try solve [ 
      fequals;
      extensionality v0;
      !matchmaker_goal ].
    all: substs.
    all: !jauto_set; tryfalse.

    + (* EvalBs P2 *)
      matchmaker H.
      all: inject_all.
      all: rewrite_Heaps.

      all: try solve [
        (!eapply B.EvalBs1); (!applys_eq B.EvalBPullOk 2 3);
        extensionality sv;
        forwards: H3 sv;
        jauto_set;
        unfolds stateUpdate; unfolds update;
        matchmaker_goal;
        (!destruct (h' sv); tryfalse);
        (!simpl; subst)
        ].

      all: try solve [
        (!applys_eq H2 2 3);
        extensionality sv;
        forwards: H3 sv;
        unfolds stateUpdate; unfolds update;
        matchmaker_goal;
        (!destruct (h' sv); tryfalse);
        (!simpl; subst)
        ].

      all: try solve [
        (!eapply B.EvalBs1); (!applys_eq B.EvalBUpdate 2 3);
        extensionality sv;
        forwards: H3 sv;
        unfolds stateUpdate; unfolds update;
        matchmaker_goal;
        (!destruct (h' sv); tryfalse);
        (!simpl; subst)
        ].

    + (* P2 invariant *)
        intros sv.
        forwards: H3 sv.
        unfolds stateUpdate; unfolds update.
        matchmaker H; inject_all.
          all: !repeat
           match goal with
          | [ |- context [match ?A with | _ => _ end] ]
          => let x    := fresh "scrut_"
          in let Heqx := fresh "Heq_" x
          in remember A as x eqn:Heqx; destruct x
           ; try matchmaker Heqx
           ; try rewrite <- Heqx in *; tryfalse
          end.
          all: inject_all.
          all: !jauto_set.

          all: try solve [ 
            fequals;
            extensionality vvvvv;
            !matchmaker_goal ].

          all: try solve [rewrite H4;
            fequals;
            extensionality vvvv;
            !matchmaker_goal].
    all: !jauto_set; tryfalse.


  - (* BlockIf - Z *)

    !jauto_set.
    + (* EvalBs P1 *)
      matchmaker H.
      all: inject_all.
      all: try doit B.EvalBIfZ.
      all: assumption.
    + (* Invariant P1 *)
      intros sv.
      matchmaker H; inject_all.
      all: forwards: H2 sv.
      all: !matchmaker_goal.
      all: !jauto_set.
      all: !inject_all.
      all: !jauto_set; tryfalse.

    + (* EvalBs P2 *)
      matchmaker H.
      all: inject_all.
      all: try doit B.EvalBIfZ.
      all: assumption.
    + (* Invariant P2 *)
      intros sv.
      matchmaker H; inject_all.
      all: forwards: H4 sv.
      all: !matchmaker_goal.
      all: !jauto_set.
      all: !inject_all.
      all: !jauto_set; tryfalse.


  - (* BlockIf - NZ *)

    !jauto_set.
    + (* EvalBs P1 *)
      matchmaker H.
      all: inject_all.
      all: try doit B.EvalBIfS.
      all: assumption.
    + (* Invariant P1 *)
      intros sv.
      matchmaker H; inject_all.
      all: forwards: H2 sv.
      all: !matchmaker_goal.
      all: !jauto_set.
      all: !inject_all.
      all: !jauto_set; tryfalse.

    + (* EvalBs P2 *)
      matchmaker H.
      all: inject_all.
      all: try doit B.EvalBIfS.
      all: assumption.
    + (* Invariant P2 *)
      intros sv.
      matchmaker H; inject_all.
      all: forwards: H4 sv.
      all: !matchmaker_goal.
      all: !jauto_set.
      all: !inject_all.
      all: !jauto_set; tryfalse.


  - (* BlockJump *)

    !jauto_set.
    + (* EvalBs P1 *)
      matchmaker H.
      all: inject_all.
      all: try doit B.EvalBJump.

      all: try solve [
          (!eapply B.EvalBs1);
          (!applys_eq B.EvalBRelease 2 3);
          extensionality sv;
          forwards: H1 sv;
          unfolds stateUpdate; unfolds update;
          matchmaker_goal;
          (!destruct (h' sv); tryfalse);
          (!simpl; subst)
        ].

      all: assumption.
    + (* Invariant P1 *)
      intros sv.
      matchmaker H; inject_all.
      all: unfolds stateUpdate; unfolds update.
      all: forwards: H1 sv.

      all: matchmaker_goal'.
      all: !jauto_set.
      all: !inject_all.
      all: !jauto_set; tryfalse.

    + (* EvalBs P2 *)
      matchmaker H.
      all: inject_all.
      all: try doit B.EvalBJump.
      all: try assumption.

      all: try solve [
          (!eapply B.EvalBs1);
          (!applys_eq B.EvalBRelease 2 3);
          extensionality sv;
          forwards: H3 sv;
          unfolds stateUpdate; unfolds update;
          matchmaker_goal;
          (!destruct (h' sv); tryfalse);
          (!simpl; subst)
        ].

    + (* Invariant P2 *)
      intros sv.
      matchmaker H; inject_all.
      all: unfolds stateUpdate; unfolds update.
      all: forwards: H3 sv.
      all: matchmaker_goal'.
      all: !jauto_set.
      all: !inject_all.
      all: !jauto_set; tryfalse.

  - (* Ignore *)
    unfolds StreamType.
    !destruct (P.StreamType P1 v) eqn:StreamType1; destruct (P.StreamType P2 v) eqn:StreamType2; tryfalse.
    jauto_set.
    assert (s0 v = NoValue).
      !forwards: H0 v.
    assert (s3 v = NoValue).
      !forwards: H2 v.
    + (* EvalBs P1 *)
          (!eapply B.EvalBs1);
          (!applys_eq B.EvalBIgnore 2 3).
          extensionality sv.
          unfolds update.
          forwards: H0 sv.

    !matchmaker_goal.

    + (* Invariant P1 *)
      unfolds update.
      intros sv.
      forwards: H0 sv.
      !matchmaker_goal; tryfalse.
      destruct (h sv); jauto_set; tryfalse.
      assert (AvailableToPull = NoValue).
        !jauto_set.
        apply H4. !substs.
      tryfalse.

      !destruct (h sv); jauto_set; tryfalse.
      substs. !inject_all.

    + (* EvalBs P2 *)
          (!eapply B.EvalBs1);
          (!applys_eq B.EvalBIgnore 2 3).
          extensionality sv.
          unfolds update.
          forwards: H2 sv.
          !matchmaker_goal.
          assert (AvailableToPull = NoValue).
            !jauto_set. tryfalse.

    + (* Invariant P2 *)
      unfolds update.
      intros sv.
      forwards: H2 sv.
      !matchmaker_goal; tryfalse.
      destruct (h sv); tryfalse.
      !destruct (h sv); tryfalse.


      assert (AvailableToPull = NoValue).
        !jauto_set.
        apply H4. !substs.
      tryfalse.

      !destruct (h sv); tryfalse.
      subst. !inject_all.
 Qed.
 Next Obligation.
  unfolds Evalish.
  jauto_set;
  try apply B.EvalBs0;
  !jauto_set.
 Qed.
End Fuse.
End Fuse.



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
      introv hEvBs hLbl hEvB.
      hint Cin_ne_Cout.

      !inverts hEvB; try destruct l; try destruct l'; inject_all; tryfalse.
      all: unfolds update; unfolds StreamType.

      all: try destruct v.
      all: matchmaker_goal'.
      !rewrite hLbl.
      !destruct n0.
    Qed.
  End Map. End Map.


  Module Eg1.
    Inductive C := C1 | C2 | C3.
    Theorem EqDec_C : EqDec C. decides_equality. Qed.

    Module M := Map.
    Check M.P.
    Definition P1 := Map.P C1 C2 EqDec_C.
    Check P1.
  End Eg1.

End Eg.