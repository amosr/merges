Require Import Merges.Tactics.
Require Import Merges.Map.
Require Import Merges.Pumping.Finite.

Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.

Module DFA (Finite_Node Finite_Alpha : Finite).

 Definition Node  := Finite_Node.T.
 Definition Alpha := Finite_Alpha.T.

 Hypothesis Eq_Node  : EqDec Node.
 Hypothesis Eq_Alpha : EqDec Alpha.

 Variable Init   : Node.
 Variable Accept : Node -> bool.

 Variable Transition : Node -> Alpha -> Node.

 Definition String := list Alpha.

 Fixpoint Run (w : String) (i : Node) : Node 
 := match w with
     | [] => i
     | (a::w') => Run w' (Transition i a)
    end.

 Definition InLanguage (w : String)
   := Accept (Run w Init).


 Theorem app_dist:
   forall (x y : String) (i : Node),
   Run y (Run x i) = Run (x ++ y) i.
 Proof.
  intros. generalize i.
  induction x; eauto.
   intros; simpl; apply IHx.
 Qed.


 Fixpoint RunSteps (w : String) (i : Node) : list Node 
 := match w with
     | [] => [i]
     | (a::w') => i :: (RunSteps w' (Transition i a))
    end.

 Definition RunSteps' w i := tail (RunSteps w i).

 Theorem RunSteps_length:
   forall (x : String) (i : Node),
   length (RunSteps x i) = length x + 1.
 Proof.
  intros x.
  induction x; intros; simpl; eauto.
 Qed.

 Theorem RunSteps'_length:
   forall (x : String) (i : Node),
   length (RunSteps' x i) = length x.
 Proof.
  intros x.
  unfold RunSteps'.
  induction x; intros; simpl; eauto.
  rewrite RunSteps_length. omega.
 Qed.

 Fixpoint last (t : Set) (x : list t) (d : t) : t
 := match x with
     | []  => d
     | a :: x' => last x' a
    end.

 Theorem last_not_empty_ignore_arg:
   forall (t : Set) (x : list t) (a b : t),
   length x > 0 ->
   last x a = last x b.
 Proof.
  intros.
  induction x; eauto.
  inversion H.
 Qed.

 Theorem Run__RunSteps:
   forall (x : String) (i empty_error : Node),
   Run x i = last (RunSteps x i) empty_error.
 Proof.
  intros x.
  induction x; eauto.

  intros.
  simpl.
  erewrite IHx.
  eauto.
 Qed.

 Theorem dupe:
   forall (i : Node) (w : String),
   length w > length Finite_Node.Values ->
   exists (n : Node),
   Finite_Node.count (RunSteps w i) n > 1.
 Proof.
  intros.
  assert (length (RunSteps w i) = length w + 1).
   apply (RunSteps_length w i).
  apply Finite_Node.pigeonhole.
  assert (length (RunSteps w i) > length w) by omega.
  eapply gt_trans. apply H1. assumption.
 Qed.


 Fixpoint repeat {A} (k : nat) (xs : list A)
 := match k with
    | 0 => []
    | S n => xs ++ repeat n xs
    end.

 Theorem repeat_run:
  forall (w : String) (i : Node) (n : nat),
  Run w i = i ->
  Run (repeat n w) i = i.
 Proof.
  induction n.
   best_bet.
  intros.
  simpl.
  rewrite <- app_dist.
  rewrite H. best_bet.
 Qed.

 Theorem split2:
   forall (w : String) (i j k : Node),
   Finite_Node.count (RunSteps w i) j > 0 ->
   Run w i = k ->
   exists (x y : String),
   w = x ++ y /\
   Run x i = j /\
   Run y j = k.
 Proof.
  induction w; intros; simpl in *.
   eexists []. eexists [].
   destruct (Finite_Node.Eq_T j i); splits; best_bet.
   simpl in *.

  destruct (Finite_Node.Eq_T j i).
   eexists []. exists (a :: w).
   splits; best_bet.

  destruct (IHw (Transition i a) j k); best_bet.
  destruct H1. destructs H1.
  exists (a :: x) x0; splits; best_bet.
 Qed.

 Theorem split3:
   forall (w : String) (i j k : Node),
   Finite_Node.count (RunSteps w i) j > 1 ->
   Run w i = k ->
   exists (x y z : String),
   w = x ++ y ++ z /\
   y <> [] /\
   Run x i = j /\
   Run y j = j /\
   Run z j = k.
 Proof.
  induction w; intros.
   simpl in *.
   destruct (Finite_Node.Eq_T j i); best_bet.
  
  simpl in *.
  destruct (Finite_Node.Eq_T j i).
   remember (split2 w).
   destruct e0 with (i := Transition i a) (j := j) (k := k); best_bet.
   destruct e1; destructs H1.
   eexists [].
   exists (a ::x) x0; splits; best_bet.

  destruct (IHw (Transition i a) j k); best_bet.
   destruct H1. destruct H1. destructs H1.
  exists (a :: x) x0 x1; splits; best_bet.
 Qed.


 Theorem pumping:
   forall (i : Node) (w : String) (k : nat),
   length w > length Finite_Node.Values ->
   exists (x y z : String),
   x ++ y ++ z = w     /\
   y <> []             /\
   Run w i = Run (x ++ repeat k y ++ z) i.
 Proof.
  intros.
  destruct (dupe i w); best_bet.
  edestruct (split3 w i x); best_bet.
  destruct H1. destruct H1. destructs H1.
  exists x0 x1 x2; splits; best_bet.
  repeat (rewrite <- app_dist).
  rewrite repeat_run; best_bet.
 Qed.

End DFA.