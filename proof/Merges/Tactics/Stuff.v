Require Import Merges.Tactics.LibTactics.
Require Import Coq.Lists.List.
Require Export Omega.

Import ListNotations.
Set Implicit Arguments.

(* I think using a prefix is a better idea than the suffix in LibTactics:
  not all tactics have "*" and "~" variants defined, and it seems inconsistent.
  At least this way it is consistently defined for all.

  However, "*" does not work as a prefix since it is a bullet.
*)
Tactic Notation "!" tactic(t) := t; auto_star.


(* *)
Ltac unfold_simp F :=
  repeat match goal with
  | |- context [F _] => unfold F; simpl
  | H : context [F _] |- _ => unfold F in H; simpl in H
  end.

(*
  Definition double n : nat := n * 2.
  Hint Extern 1 => unfold_simp double.
*)


Ltac destruct_t T :=
  repeat match goal with
  | [ |- context [ ?V ] ]
  => match type of V with T => destruct V end
  (* | [ context [ ?V ] |- _ ]
  => match type of V with T => destruct V *)
  end.


Ltac crunch_destruct V :=
 repeat (match goal with
  | [ |- context [ V ?X          ] ] => destruct (V X)
  | [ |- context [ V ?X ?Y       ] ] => destruct (V X Y)
  | [ |- context [ V ?X ?Y ?Z    ] ] => destruct (V X Y Z)
  | [ |- context [ V ?X ?Y ?Z ?U ] ] => destruct (V X Y Z U)
  end).

Ltac bye_not_eq :=
 try solve
 [ substs;
   match goal with
    H : ?x <> ?x |- _
    => destruct H; reflexivity
   end].

Ltac bye_in_empty :=
 try solve
 [ substs;
   match goal with
    H : In ?x [] |- _
    => inverts H
   end].

Ltac injects H :=
   injection H; clear H; intros; subst.

(*

Ltac bye_punch_ne :=
 try solve [
 match goal with 
  | H : ?a = ?c |- ?a <> ?b
  => rewrite H; intros not; inversion not
  | H : ?c = ?a |- ?a <> ?b
  => rewrite H; intros not; inversion not
  | H : ?b = ?c |- ?a <> ?b
  => rewrite H; intros not; inversion not
  | H : ?c = ?b |- ?a <> ?b
  => rewrite H; intros not; inversion not
 end].
*)


Ltac best_bet :=
  eauto; try solve [simpl in *; try omega; bye_not_eq; bye_in_empty; congruence].

Tactic Notation "churn_with" tactic(F) :=
  repeat (F; best_bet; simpl in *).


