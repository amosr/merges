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

  Variable StreamV : Set.
  Variable StreamVEqDec : EqDec StreamV.

  Definition Heap := Map StreamV (list Value).
  Definition Pred := Heap -> Prop.

  Let streamUpdate := Map.update StreamV (list Value) StreamVEqDec.

  Inductive StreamTypeT :=
   | Input | Output | Ignore.
  Variable StreamType : StreamV -> StreamTypeT.

  Inductive Block : Type :=
   (* Blocking pull, wait forever until we get something *)
   | BlockPull : StreamV -> Label -> Block
   (* Release the thing we just pulled.
      When two machines are pulling from same thing, this
      signals to other machine that it can now pull if it wants *)
   | BlockRelease : StreamV -> Label -> Block
   (* Push a constant value *)
   | BlockPush : StreamV -> Value -> Label -> Block
   (* Jump to another label without doing anything *)
   | BlockJump   : Label -> Block
   .

  Variable Blocks : Label -> Block.
  Variable LabelPre  : Label -> Pred.

  Inductive EvalB : Heap -> Label
                 -> Heap -> Label -> Prop :=
   | EvalBPullOk l v lok i h
      : Blocks l = BlockPull v lok
     -> StreamType v = Input
     -> EvalB h l
              (streamUpdate v (h v ++ [i]) h) lok

   (* Release does nothing *)
   | EvalBRelease l v l' h
      : Blocks l = BlockRelease v l'
     -> StreamType v = Input
     -> EvalB h l
              h l'

   | EvalBPush l v push l' h
      : Blocks l = BlockPush v push l'
     -> StreamType v = Output
     -> EvalB h l
              (streamUpdate v (h v ++ [push]) h) l'

   | EvalBJump l l' h
      : Blocks l = BlockJump l'
     -> EvalB h l
              h l'

   | EvalBIgnore l v i h
      : StreamType v = Ignore
     -> EvalB h l
              (streamUpdate v (h v ++ [i]) h) l
   .
  Hint Constructors EvalB.

  Variable Init : Label.
  Variable InitPre : LabelPre Init (fun _ => []).

  Inductive EvalBs : Heap -> Label -> Prop :=
   | EvalBs0
      : EvalBs (fun _ => []) Init
   | EvalBs1 l l' h h'
      : EvalBs h l
     -> EvalB  h l h' l'
     -> EvalBs h' l'
   .
  Hint Constructors EvalBs.

  Definition BlocksPreT :=
    forall h h' l l',
    EvalBs h l ->
    LabelPre l h ->
    EvalB  h l h' l' ->
    LabelPre l' h'.

  Hypothesis BlocksPre: BlocksPreT.


  (*
  This is not true, since BlockPull does not require StreamType v = Input,
  but EvalB does.
  I don't think this is a real problem though, it wasn't used in any
  of the earlier proofs.

  Theorem EvalB_Step l h
         : exists l' h'
         , EvalB h  l h' l'.
  *)

  Theorem EvalBs_Hoare l h
   (hEvB : EvalBs h l)
         : LabelPre l h.
  Proof.
   !induction hEvB.
  Qed.
End Machine.

End Base.

Module Program.
 Module B := Base.

 Record Program (Label : Set) (StreamVar : Set) : Type
  := mkProgram
   { Init     : Label
   ; Blocks   : Label -> B.Block Label StreamVar

   ; StreamVarEqDec : EqDec StreamVar
   ; StreamType : StreamVar -> B.StreamTypeT

   ; LabelPre : Label -> B.Pred StreamVar
   ; BlocksPre: B.BlocksPreT StreamVarEqDec StreamType Blocks LabelPre Init
   ; InitPre  : LabelPre Init (fun _ => [])
   }.

  Definition EvalBs (Label : Set) (StreamVar : Set) (P : Program Label StreamVar)
   := B.EvalBs (StreamVarEqDec P) (StreamType P) (Blocks P) (Init P).

End Program.


Module Fuse.
  Module B := Base.
  Module P := Program.

  Parameter SV : Set.
  Parameter L1 : Set.
  Parameter P1 : P.Program L1 SV.

  Parameter L2 : Set.
  Parameter P2 : P.Program L2 SV.

  (* Figure out what the fused StreamType will be *)
  Definition StreamType (s : SV) : B.StreamTypeT :=
  match P.StreamType P1 s, P.StreamType P2 s with
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
    | FakeValue
    | HaveValue
    | NoValue
    .

  Inductive IsValid :=
    | Valid
    | INVALID
    .

  Inductive L' :=
    | LX (l1 : L1) (l2 : L2) (s1 : SV -> State) (s2 : SV -> State) (v : IsValid).

  Definition stateUpdate := Map.update SV State (P.StreamVarEqDec P1).
  Check stateUpdate.

  Inductive BlockOption :=
    | BlockOk (b : B.Block L' SV)
    | BlockTryOther
    | BlockINVALID
    .

  Definition makeBlock
    (LA : Set)
    (mkLabel : LA -> (SV -> State) -> (SV -> State) -> L')
    (block : B.Block LA SV)
    (sThis sOther : SV -> State)
    (typeThis : SV -> B.StreamTypeT)
    (typeOther : SV -> B.StreamTypeT)
           : BlockOption :=
   match block with
    | B.BlockJump _ l'
    => BlockOk (B.BlockJump _ (mkLabel l' sThis sOther))

    (* Releases are fairly simple, so let's start with them *)
    | B.BlockRelease sv l'
    => match typeThis sv, typeOther sv, sThis sv with
       (* If the other machine ignores this, we can just release as normal *)
       (* We require sThis to be 'NoValue' even though there is something: *)
       (* it doesn't need to be tracked because it's ignored *)
       | B.Input, B.Ignore, NoValue
       => BlockOk (B.BlockRelease sv (mkLabel l' sThis sOther))

       (* Both machines want to pull from this, so let's see.
          This machine must have a value for sv in its state now:
          sThis sv = HaveValue
          But it depends whether the other machine has it
       *)
       | B.Input, B.Input, HaveValue
       => match sOther sv with
          (* If other machine still has one, we only pretend to release *)
          | HaveValue
          | FakeValue
          => BlockOk (B.BlockJump _ (mkLabel l' (stateUpdate sv NoValue sThis) sOther))
          (* Other machine has already pretended to release *)
          | NoValue
          => BlockOk (B.BlockRelease sv (mkLabel l' (stateUpdate sv NoValue sThis) sOther))
          end

       (* The other machine has pushed this, so only pretend release *)
       | B.Input, B.Output, HaveValue
       => BlockOk (B.BlockJump _ (mkLabel l' (stateUpdate sv NoValue sThis) sOther))

       (* Otherwise sThis sv is invalid *)
       | _, _, _
       => BlockINVALID
       end

    (* Pulls are a bit more interesting *)
    | B.BlockPull sv l'
    => match typeThis sv, typeOther sv, sThis sv with
       (* Ignore is easy *)
       | B.Input, B.Ignore, NoValue
       => BlockOk (B.BlockPull sv (mkLabel l' sThis sOther))

       (* Both machines want to pull from this, so let's see. *)
       (* We already have a fake one, ready to go. Just a jump *)
       | B.Input, B.Input, FakeValue
       => BlockOk (B.BlockJump _ (mkLabel l' (stateUpdate sv HaveValue sThis) sOther))
       | B.Input, B.Input, NoValue
       => match sOther sv with
          (* If other machine has one but we don't, that means
             we have already pulled and released, but they haven't released yet.
             They need to run a bit and hopefully release.
           *)
          | HaveValue
          | FakeValue
          => BlockTryOther
          (* Neither machine has it, but we both want it.
             We end up with a real value, and them a fake. *)
          | NoValue
          => BlockOk (B.BlockPull sv (mkLabel l' (stateUpdate sv HaveValue sThis) (stateUpdate sv FakeValue sOther)))
          end

       (* The other machine must push. Have they given us anything yet? *)
       | B.Input, B.Output, NoValue
       => match sThis sv with
          (* Yes. We have a fake value on top, so we can turn it into a real one *)
          | FakeValue
          => BlockOk (B.BlockJump _ (mkLabel l'  (stateUpdate sv HaveValue sThis) sOther))
          (* We can't have a real one yet!!! *)
          | HaveValue
          => BlockINVALID
          (* No, we have to wait. Try to let the other machine run *)
          | NoValue
          => BlockTryOther
          end

       (* Otherwise sThis sv is invalid *)
       | _, _, _
       => BlockINVALID
       end

    (* Pushes are pretty similar *)
    | B.BlockPush sv v l'
    => match typeThis sv, typeOther sv, sThis sv with
       (* Ignore is easy *)
       | B.Output, B.Ignore, NoValue
       => BlockOk (B.BlockPush sv v (mkLabel l' sThis sOther))
       (* Check if the other machine is ready to scoop a new one *)
       | B.Output, B.Input, NoValue
       => match sOther sv with
          (* No. The other machine has a value it hasn't already used *)
          | HaveValue
          | FakeValue
          => BlockTryOther
          (* Other machine is empty and ready to receive *)
          | NoValue
          (*=> BlockOk (B.BlockJump _ (mkLabel l' sThis (stateUpdate sv FakeValue sOther)))*)
          => BlockOk (B.BlockPush sv v (mkLabel l' sThis (stateUpdate sv FakeValue sOther)))
          end
       (* Both programs cannot push to the same output *)
       | _, B.Output, _
       => BlockINVALID
       (* sThis sv is invalid *)
       | _, _, _
       => BlockINVALID
       end
   end.


  Definition Blocks (l : L') : B.Block L' SV :=
   match l with
   | LX l1 l2 s1 s2 v
   => let invalid := B.BlockJump _ (LX l1 l2 s1 s2 INVALID) in
      match v
    , makeBlock (fun l1' s1' s2' => LX l1' l2 s1' s2' Valid) (P.Blocks P1 l1) s1 s2 (P.StreamType P1) (P.StreamType P2)
    , makeBlock (fun l2' s2' s1' => LX l1 l2' s1' s2' Valid) (P.Blocks P2 l2) s2 s1 (P.StreamType P2) (P.StreamType P1)
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


  Definition Evalish (LA : Set) (P : P.Program LA SV) (s : SV -> State) (iss : B.Heap SV) (l : LA) : Prop :=
   exists iss',
  (* It turns out the proof is slightly easier if we put the EvalBs first.
     Because the EvalBs is more likely to instantiate the existential *)
    P.EvalBs P iss' l /\
    (forall sv,
     match s sv with
      | FakeValue => exists i, iss sv = iss' sv ++ [i]
      | HaveValue => iss' sv = iss sv
      | NoValue   => iss' sv = iss sv
     end /\
     (P.StreamType P sv = B.Ignore -> s sv = NoValue)
     ).

  Definition LabelPre (l : L') : B.Pred SV :=
   match l with
   | LX l1 l2 s1 s2 INVALID
   => fun _ => True
   | LX l1 l2 s1 s2 Valid
   => fun iss
   => Evalish P1 s1 iss l1
   /\ Evalish P2 s2 iss l2
   end.
  Hint Unfold LabelPre.


  Program Definition r
  := {| P.Blocks := Blocks
      ; P.LabelPre := LabelPre
      ; P.Init := LX (P.Init P1) (P.Init P2) (fun _ => NoValue) (fun _ => NoValue) Valid
      ; P.StreamType := StreamType
      ; P.StreamVarEqDec := P.StreamVarEqDec P1
      |}.

  Next Obligation.
   Ltac doit X := try solve [(!eapply B.EvalBs1); (!eapply X)].


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
  end.



   unfolds B.BlocksPreT.
   introv hEvBs hLbl hEvB.
   clear hEvBs.
   destruct l; destruct l'.
   !destruct v0; destruct v; try solve [inverts hEvB; tryfalse].

   simpls; unfolds Evalish; unfolds Blocks; unfolds makeBlock.

  inverts hEvB.
  - (* BlockPull *)
    symmetry in H0.
    symmetry in H; matchmaker H.
    all: inject_all.
    all: !jauto_set
      ; doit B.EvalBPullOk
      ; doit B.EvalBIgnore
      ; try assumption
      .

    all: intros; unfolds stateUpdate; forwards: H0 sv; forwards: H2 sv.
    all: try match goal with
          | [ |- context [match update SV _ _ ?A _ _ ?B with | _ => _ end] ]
          => destruct (P.StreamVarEqDec P1 A B); substs
         end; substs.
    all: jauto_set.
    all: repeat match goal with
    | [ ABC : _ = _  |- _]
    => rewrite <- ABC in *
    end.
    all: !intros; jauto.
    all: tryfalse.
    all: !repeat rewrite update_eq_is.
    all: try solve [!repeat rewrite update_ne_is].

    all: try match goal with
          | [ |- context [update SV _ _ ?A _ _ ?B] ]
          => destruct (P.StreamVarEqDec P1 A B); substs
         end; !substs.
    all: !repeat rewrite update_eq_is.
    all: try solve [!repeat rewrite update_ne_is].

    all: !repeat match goal with
    | [ ABC : _ = _  |- _]
    => rewrite <- ABC in *
    end.

    all: !try match goal with
          | [ ABC : (?A = ?A) -> _ = _ |- _]
          => !rewrite ABC in *
         end.

    all: !repeat match goal with
    | [ ABC : _ = _  |- _]
    => rewrite <- ABC in *
    end.



  - (* BlockRelease *)
    symmetry in H0.
    symmetry in H; matchmaker H.
    all: inject_all.
    all: !jauto_set
      ; doit B.EvalBRelease
      ; try assumption
      .
    all: !intros; jauto_set.

    all: !intros.
    all: unfolds stateUpdate; forwards: H0 sv; forwards: H2 sv.

    all: try match goal with
          | [ |- context [update SV _ _ ?A _ _ ?B] ]
          => destruct (P.StreamVarEqDec P1 A B); substs
         end; !substs.
    all: !repeat rewrite update_eq_is.
    all: try solve [!repeat rewrite update_ne_is].

    all: !jauto_set.
    all: !repeat match goal with
    | [ ABC : _ = _  |- _]
    => rewrite <- ABC in *
    end.

  - (* BlockPush *)
    symmetry in H0.
    symmetry in H; matchmaker H.
    all: inject_all.
    all: !jauto_set
      ; doit B.EvalBIgnore
      ; doit B.EvalBPush
      .
    all: !intros; unfolds stateUpdate; forwards: H0 sv; forwards: H2 sv; jauto_set.

    all: try match goal with
          | [ |- context [update SV _ _ ?A _ _ ?B] ]
          => destruct (P.StreamVarEqDec P1 A B); substs
         end; !substs.
    all: !repeat rewrite update_eq_is.
    all: try solve [!repeat rewrite update_ne_is].

    all: !repeat match goal with
    | [ ABC : _ = _  |- _]
    => rewrite <- ABC in *
    end.
    all: !try match goal with
          | [ ABC : (?A = ?A) -> _ = _ |- _]
          => !rewrite ABC in *
         end.
    all: !repeat match goal with
    | [ ABC : _ = _  |- _]
    => rewrite <- ABC in *
    end.

    all: intros; tryfalse.

  - (* BlockJump *)
    symmetry in H; matchmaker H.
    all: inject_all.
    all: jauto_set_hyps; intros.
    all: try (forwards: H0 s; forwards: H0 s4; forwards: H2 s; forwards: H2 s4).
    all: jauto_set_hyps.
    all: intros.

    all: !repeat match goal with
    | [ ABC : _ = _  |- _]
    => rewrite <- ABC in *
    end.
    all: !try match goal with
          | [ ABC : (?A = ?A) -> _ = _ |- _]
          => !rewrite ABC in *
         end.
    all: !repeat match goal with
    | [ ABC : _ = _  |- _]
    => rewrite <- ABC in *
    end.

    all: !jauto_set.
    all: doit B.EvalBJump.
    all: doit B.EvalBPullOk.
    all: doit B.EvalBIgnore.
    all: doit B.EvalBRelease.
    all: doit B.EvalBPush.

    all: !intros; unfolds stateUpdate; forwards: H0 sv; forwards: H2 sv; jauto_set.
    all: !intros; tryfalse.

    all: !repeat match goal with
    | [ ABC : _ = _  |- _]
    => rewrite <- ABC in *
    end.
    all: jauto_set.

    all: try match goal with
          | [ |- context [update SV _ _ ?A _ _ ?B] ]
          => destruct (P.StreamVarEqDec P1 A B); substs
         end; !substs.


    all: !repeat rewrite update_eq_is.
    all: try solve [!repeat rewrite update_ne_is].
    all: tryfalse.
    all: !repeat match goal with
    | [ ABC : _ = _  |- _]
    => rewrite <- ABC in *
    end.

    jauto_set. rewrite H3.
    (* x sv ++ [?i] = x sv ++ [x1] *)
    (* > reflexivity *)
    (* Unable to unify "?i" with "x1" (cannot instantiate "?i" because "x1" is not in its scope *)
    (* But can't move the x1 existential, or the i existential in, because
       we need "sv" to be able to get "x1", but "sv" is inside the i existential.
       I am sure there is a way around this, it just requires rejigging the invariants *)
    skip.

  - (* Ignore! *)
    unfolds StreamType.
    !destruct (P.StreamType P1 v) eqn:StreamType1; destruct (P.StreamType P2 v) eqn:StreamType2; tryfalse.
    jauto_set.
    all: doit B.EvalBIgnore.
    all: intros.
    all: forwards: H0 sv; forwards: H2 sv.
    all: !jauto_set.
    all: destruct (P.StreamVarEqDec P1 v sv); substs.
    all: !repeat rewrite update_eq_is.
    all: try solve [!repeat rewrite update_ne_is].
    
    all: rewrite StreamType1 in *.
    all: rewrite StreamType2 in *.
    !rewrite H5 in *.
    rewrite H4. reflexivity.

    !rewrite H7 in *.
    rewrite H6. reflexivity.
 Grab Existential Variables.
    apply 0.
 Qed.
 Next Obligation.
  unfolds Evalish.
  jauto_set;
  try apply B.EvalBs0;
  !jauto_set.
 Qed.
End Fuse.


