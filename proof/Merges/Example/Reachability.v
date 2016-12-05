(* Stashed reachability stuff *)
Require Import Merges.Tactics.
Require Import Merges.Map.

Require Import Merges.Machine.
Require Import Merges.Fusion.
Require Import Merges.Example.Base.
Require Import Merges.Example.Combinators.


Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ClassicalDescription.

Module Reachability.
Section Reachability.

  Variable L : Set.
  Variable C : Set.
  Variable V : Set.
  Variable P : P.Program L C V.

  Let ShitSet := L -> bool.

  Variable EqDec_L : EqDec L.

  Let empty := fun (_ : L) => false.

  Definition outlabels (l : L) : list L :=
  match P.Blocks P l with
   | B.BlockPull _ _ l' => [l']
   | B.BlockRelease _ _ l' => [l']
   | B.BlockPush _ _ l' => [l']
   | B.BlockUpdate _ _ _ l' => [l']
   | B.BlockIf _ _ lz ls => [lz; ls]
   | B.BlockJump _ _ l' => [l']
  end.

  Fixpoint step (n : nat) (ls : list L) (s : ShitSet) : ShitSet :=
  match n with
  | 0 =>
    s
  | S n' =>
    match ls with
    | [] =>
      s
    | l::ls' =>
      match s l with
      | true =>
        step n' ls' s
      | false =>
        let s'   := update _ _ EqDec_L l true s
     in let ls'' := ls' ++ outlabels l
     in step n' ls'' s'
      end
    end
  end.

  Definition reach (n : nat) := step n [P.Init P] empty.

  Definition FiniteReachable n := reach n = reach (S n).

End Reachability.
End Reachability.

Inductive C := C1 | C2.
Theorem EqDec_C : EqDec C.
Proof.
  decide_equality_simpl.
Defined.


Theorem EqDec_MapL : EqDec Map.L.
Proof.
  decide_equality_simpl.
Defined.

Module M := Map.

Theorem C1_ne_C2 : C1 <> C2. Proof. intros X. inverts X. Qed.

Definition P1 := Map.P EqDec_C (fun x => S x) C1_ne_C2.

Theorem ReachP1 : Reachability.FiniteReachable P1 EqDec_MapL 3.
Proof.
 unfolds.
 extensionality x.
 unfolds.
 simpl.
 unfolds update.
 matchmaker_goal; !tryfalse.
Qed.

Theorem ReachP1_L'Pull: Reachability.reach P1 EqDec_MapL 3 Map.L'Pull = true.
Proof.
  unfolds Reachability.reach.
  simpl.
  unfolds update.
  !simpl.
Qed.

(*



Theorem eval_ok: forall l h sh,
 P.EvalBs P' h sh l -> l <> F.L'INVALID _ _ _.
Proof.
  intros.
  unfolds P.EvalBs.
  simpls.
  induction H.
    unfolds F.Init. intros X. tryfalse.

    destruct l; tryfalse.
    intros X.
    destruct l'; tryfalse.

    apply B.EvalBs_Hoare with (LabelPre := P.LabelPre P') in H;
      try solve [apply P.InitPre];
      try solve [apply P.BlocksPre].
    simpls.

    destruct H as [hPre1 hPre2].
    destruct hPre1 as [hEv1 hPre1].
    destruct hPre2 as [hEv2 hPre2].

(*
    inverts H0;
      try solve
        [ simpls
        ; matchmaker H
        ].
*)
  skip.

Qed.

*)

(*
Theorem ReachP' : Reachability.FiniteReachable P' EqDec_L.
Proof.
 unfolds.
 exists 1.
  unfolds.
  simpl.
  extensionality x.
  unfolds update.
  matchmaker_goal; !tryfalse.
Qed.
*)