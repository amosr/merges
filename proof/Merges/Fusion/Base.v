(* Multiple inputs and outputs, blocking reads *)
Require Import Merges.Tactics.
Require Import Merges.Map.

Require Import Merges.Machine.


Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.
Require Import Coq.Logic.FunctionalExtensionality.


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
  (* XXX TODO: this should be if either machine = Ignore, s sv = NoValue.
    This is because if other machine ignores the input, there is no scheduling to do.
  *)

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

  Definition Init := LX (P.Init P1) (P.Init P2) (fun _ => NoValue) (fun _ => NoValue) Valid.
  Hint Unfold Init.
End Fuse.
End Fuse.
