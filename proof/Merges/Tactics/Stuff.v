Require Import Merges.Tactics.LibTactics.
Require Import Coq.Lists.List.
Require Export Omega.

Import ListNotations.
Set Implicit Arguments.

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


