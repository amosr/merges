Require Import Merges.Tactics.
Require Import Merges.Map.

Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.

Section Reorder.
 Variable Alphabet : Set.
 Variable Language : list Alphabet -> Prop.


 Inductive Accept : list Alphabet -> list Alphabet -> list Alphabet -> Prop :=
 | D'Empty : Accept [] [] []
 | D'Pop xs ys s ss : Accept xs ys ss -> Accept xs (s :: ys) (s :: ss)
 | D'Rot xs ys s ss : Accept xs ys (s :: ss) -> Accept xs ys (ss ++ [s])
 | D'Push xs ys s ss
    : not (In s ss)
    -> Accept xs ys (s :: ss)
    -> Accept (s :: xs) ys ss
 .
 Hint Constructors Accept.
 
 Definition AcceptTop xs ys := Accept xs ys [].
 
 Theorem Accept_sym u: Accept u u [].
 Proof.
  !induction u.
 Qed.
 
 Theorem Accept_weaken u v s ss
  :  Accept u v ss
  -> Accept u (s :: v) (s :: ss).
 Proof.
  intros.
  !induction H.
 Qed.
 
(*
 
 Theorem Accept_reorder u v s1 s2 s
  :  Accept u v (s :: s1 ++ s2) -> Accept u v (s1 ++ [s] ++ s2).
 Proof.
  intros.
  gen u v s1 s2 s.
  induction s1.
  !simpls; intros.
  !simpls; intros.

   apply D'Rot.
   applys_eq IHs1 1.
      apply D'Rot.

    !inverts H.
   !inversion H; subst.
   !inversion H3; subst.
   simpls. eauto.
   simpls. eauto.
   !induction s1; simpls.
  induction H.
  gen u v s2.
  induction s1; !intros.
  simpls.
  !rewrite <- app_nil_end.
  
  apply D'Rot.

 Theorem Accept_reorder u v s1 s2
  :  Accept u v (s1 ++ s2) <-> Accept u v (s2 ++ s1).
 Proof.
  intros.
  gen u v s2.
  induction s1; intros; split; intros.
  !rewrite <- app_nil_end.
  !rewrite app_nil_end.

 simpls.

  rewrite <- IHs1 in H.
  !induction u.
  induction H.
 Qed.

 Theorem Accept_app u u' v v' s: Accept u u' [] -> Accept v v' []
   -> Accept (u ++ v) (u' ++ v') [].
 Proof.
  intros.
  gen v v' s.
  !induction H; intros.
  !simpl.
  apply D'Pop.
  constructor.
*)