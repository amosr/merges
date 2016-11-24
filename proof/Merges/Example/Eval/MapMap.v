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


  Fixpoint step (n : nat) (l : L) (s : ShitSet) : ShitSet :=
  match s l with
  | true => s
  | false =>
    let s' := update _ _ EqDec_L l true s in
    match n with
    | 0
    => s'
    | S n'
    => match P.Blocks P l with
       | B.BlockPull _ _ l' => step n' l' s'
       | B.BlockRelease _ _ l' => step n' l' s'
       | B.BlockPush _ _ l' => step n' l' s'
       | B.BlockUpdate _ _ _ l' => step n' l' s'
       | B.BlockIf _ _ lz ls => step n' lz (step n' ls s')
       | B.BlockJump _ _ l' => step n' l' s'
       end
    end
  end.

  Definition reach (n : nat) := step n (P.Init P) empty.

  Definition FiniteReachable := exists n, reach n = reach (S n).

End Reachability.
End Reachability.

Inductive C := C1 | C2 | C3.
Theorem EqDec_C : EqDec C. decides_equality. Qed.

Module M := Map.

Theorem C1_ne_C2 : C1 <> C2. Proof. intros X. inverts X. Qed.
Theorem C2_ne_C3 : C2 <> C3. Proof. intros X. inverts X. Qed.

Definition P1 := Map.P EqDec_C (fun x => S x) C1_ne_C2.
Definition P2 := Map.P EqDec_C (fun x => S x) C2_ne_C3.

Definition P' := r P2 P1 EqDec_C.
(* XXX need to add 'priority' to fusion algorithm, so HaveValue Pull > NoValue Pull,
  so that evaluation order for above is more natural
  for now, fuse "P2 P1" instead of "P1 P2" to force order.
 *)

Theorem EqDec_All A (n m : A) : { n = m } + {n <> m}.
Proof.
 !destruct (excluded_middle_informative (n = m)).
Qed.

Definition EqDec_L := @EqDec_All (F.L' C Map.L Map.L).


Theorem ReachP1 : Reachability.FiniteReachable P1 (@EqDec_All Map.L).
Proof.
 unfolds.
 exists 2.
  unfolds.
  extensionality x.
  simpl.
  unfolds update.
  matchmaker_goal; !tryfalse.
Qed.

Theorem ReachP1_L'Pull: Reachability.reach P1 (@EqDec_All Map.L) 2 Map.L'Pull = true.
Proof.
  unfolds Reachability.reach.
  simpl.
  unfolds update.
  matchmaker_goal; !tryfalse.
Qed.

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
    
    
    inverts H0;
      try solve
        [ simpls
        ; matchmaker H
        ].
  skip.

Qed.


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

Theorem eval_P'_1':
  exists sh,
 EvalTop P'
  (fun c => match c with
            | C1 => [11; 1]
            | C2 => [12; 2]
            | C3 => [13; 3]
            end)
  sh (P.Init P').
Proof.
  eexists.
  evalsB1 C B.EvalBPullOk.
  evalsB1 C B.EvalBUpdate.
  evalsB1 C B.EvalBPush.
  evalsB1 C B.EvalBUpdate.
  evalsB1 C B.EvalBPush.
  evalsB1 C B.EvalBJump.
  evalsB1 C B.EvalBRelease.

  evalsB1 C B.EvalBPullOk.
  evalsB1 C B.EvalBUpdate.
  evalsB1 C B.EvalBPush.
  evalsB1 C B.EvalBUpdate.
  evalsB1 C B.EvalBPush.
  evalsB1 C B.EvalBJump.
  evalsB1 C B.EvalBRelease.

  applys_eq EvalsB0 0; !fequals.

  repeat (funfolds; simpls).
  !fequals.
  extensionality c.
  repeat destruct_t (EqDec C); !tryfalse.

  extensionality c; !matchmaker_goal.

  extensionality c; funfolds; !matchmaker_goal.
Qed.

