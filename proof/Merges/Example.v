Require Import Merges.Tactics.
Require Import Merges.Map.

Require Import Merges.Machine.
Require Import Merges.Fusion.


Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.
Require Import Coq.Logic.FunctionalExtensionality.


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
      introv hLbl hEvB.
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

    Theorem C1_ne_C2 : C1 <> C2. Proof. intros X. inverts X. Qed.
    Theorem C2_ne_C3 : C2 <> C3. Proof. intros X. inverts X. Qed.

    Definition P1 := Map.P EqDec_C (fun x => S x) C1_ne_C2.
    Definition P2 := Map.P EqDec_C (fun x => S x) C2_ne_C3.

    Definition P' := r P1 P2 EqDec_C.

    Print P'.
    Check P.EvalBs.
    Print Tactics.

    Ltac sunfolds X := unfolds X; simpls.


    (* XXX TODO: change Fusion.Base.LabelPre to be "if either machine ignores input, state = NoValue" *)

(*

    Theorem all_eval_ok h sh l:
     P.EvalBs P' h sh l ->
     Tactics.isValid l.
    Proof.
      intros hEvBs.
      induction hEvBs; !simpls.

      destruct l as [l1 l2 s1 s2 v] eqn:hl.
      destruct l' as [l'1 l'2 s'1 s'2 v'] eqn:hl'.
      destruct v; !destruct v'; tryfalse.

      sunfolds F.Blocks.
      sunfolds F.makeBlock.
      sunfolds Map.Blocks.

      sunfolds F.StreamType.
      sunfolds Map.StreamType.

      inverts H.

(*
      all: time try solve [clear hEvBs; clear H1; time matchmaker H0].
      clear hEvBs; time matchmaker H0.
*)
    skip. skip. skip. skip. skip. skip.

    apply Base.EvalBs_Hoare with (LabelPre := F.LabelPre P1 P2)
    in hEvBs;
    try solve [apply P'].

  simpls.
  sunfolds F.Evalish.
  destruct hEvBs as [hPre1 hPre2].
  destruct hPre1 as [hEv1 hPre1].
  destruct hPre2 as [hEv2 hPre2].

  forwards: hPre1 C1.
  forwards: hPre1 C2.
  forwards: hPre1 C3.

  forwards: hPre2 C1.
  forwards: hPre2 C2.
  forwards: hPre2 C3.

  clear hPre1. clear hPre2.
  clear hEv1. clear hEv2.

  jauto_set.

  unfolds Map.StreamType.

  destruct l1; destruct l2; repeat (destruct (EqDec_C _ _); tryfalse).
  - 
    assert (s1 C1 = F.NoValue).
    !destruct (s1 C1).
    + destruct (h' C1); tryfalse.

  repeat match goal with
    | [ H : (P.EvalBs _ _ _ _) |- _ ]
    => clear H
    | [ H : (?A = ?A) |- _ ]
    => clear H
    | [ H : True |- _ ]
    => clear H
    | [ H : (?A = ?A -> ?B) |- _ ]
    => let H' := fresh H in !assert B as H'; clear H; rewrite H' in *
  end.


  rewrite H6 in *.

  time matchmaker H0.

  - 
  inject_all.

  repeat match goal with
    | [ H : _ <> _ |- _ ]
    => clear H
    | [ H : _ = EqDec_C _ _ |- _ ]
    => clear H
    | [ H : (?A = ?A) |- _ ]
    => clear H
  end.

  rewrite <- Heq_scrut_Heq_scrut_H9 in *.
  rewrite <- Heq_scrut_Heq_scrut_H3 in *.
  rewrite <- Heq_scrut_Heq_scrut_H8 in *.

  repeat match goal with
    | [ H : s'1 _ = _ |- _ ]
    => try rewrite H in *; clear H
    | [ H : s'2 _ = _ |- _ ]
    => try rewrite H in *; clear H
    | [ H : _ = s'1 _ |- _ ]
    => try rewrite <- H in *; clear H
    | [ H : _ = s'2 _ |- _ ]
    => try rewrite <- H in *; clear H
  end.

  !destruct (h' C2).
  !destruct (s'2 C3).

  rewrite <- Heq_scrut_Heq_scrut_H9 in *.

  repeat match goal with
    | [ H : _ <> _ |- _ ]
    => clear H
  end.

  clear n6.

  (* 251s *)

Ltac matchmaker' Heq :=
 match goal with
| [ Heq : _ = match ?A with | _ => _ end |- _ ]
=> let x    := fresh "scrut_" Heq
in let Heqx := fresh "Heq_" x
in remember A as x eqn:Heqx; destruct x; tryfalse; try rewrite <- Heqx in *
 ; try matchmaker Heqx
| [ Heq : match ?A with | _ => _ end = _ |- _ ]
=> let x    := fresh "scrut_" Heq
in let Heqx := fresh "Heq_" x
in remember A as x eqn:Heqx; destruct x; tryfalse; try rewrite <- Heqx in *
 ; try matchmaker Heqx
end.


  time matchmaker' H0.
  (* 226s *)
*)
  End Eg1.
End Eg.