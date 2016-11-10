Require Import Merges.Tactics.
Require Import Merges.Map.

Require Import Merges.List.List.
Require Import Merges.List.Index.

Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.



Module Type Finite.
 Variable T : Set.
 Variable Values : list T.
 Hypothesis Eq_T      : EqDec T.

 Fixpoint count (l : list T) (t : T) : nat
 := match l with
    | [] => 0
    | (x::l') => if Eq_T t x
                 then S (count l' t)
                 else    count l' t
    end.

 Theorem count__In (l : list T) (t : T):
   count l t > 0 <-> In t l.
 Proof.
  split; induction l; intros;
  simpl in *;
  destroy_eqdecs Eq_T;
  best_bet.
  destruct H; best_bet.
 Qed.

 Hypothesis Includes : forall (s : T), count Values s = 1.

 Fixpoint remove (t : T) (l : list T) : list T :=
  match l with
  | [] => []
  | (x::xs) => if   Eq_T x t
               then remove t xs
               else x :: remove t xs
  end.

 Theorem remove_no_change (l : list T) (t u : T) (Hne : t <> u):
   In t l <-> In t (remove u l).
 Proof.
  induction l; split; intros; simpl in *; best_bet; destroy_eqdecs Eq_T;
  simpl;
  try apply IHl;
  try destruct H;
  try solve [right; apply IHl; best_bet];
  best_bet.
 Qed.
 
 Theorem remove_not_in__length (l : list T) (t : T):
   ~In t l ->
   length l = length (remove t l).
 Proof.
  intros.
  induction l.
  eauto.
  simpl in *.
  destroy_eqdecs Eq_T.
  destruct H. eauto.
  simpl.
  rewrite IHl; eauto.
 Qed.

 Theorem remove_in__dec_count (l : list T) (t : T):
   In t l ->
   length l > length (remove t l).
 Proof.
  intros.
  induction l; bye_in_empty.
  simpl in *.
  destruct H; destroy_eqdecs Eq_T;
  destruct (In_or_not t l Eq_T);
  try apply IHl in H;
  try apply IHl in H0;
  try apply remove_not_in__length in H0;
  best_bet.
 Qed.


 Theorem remove_ne_no_change (l : list T) (t u : T):
   t <> u ->
   count l t = count (remove u l) t.
 Proof.
  intros; induction l; churn_with (destroy_eqdecs Eq_T).
 Qed.

 Theorem pigeonhole_impl (uniques multi : list T):
   (forall s : T, In s multi -> count uniques s = 1) ->
   length multi > length uniques ->
   exists (t : T), count multi t > 1.
 Proof.
  clear.
  gen uniques.
  induction multi; intros; simpl in *.
   omega.

  destruct (In_or_not a multi Eq_T).
  assert (count multi a > 0).
  apply count__In. assumption.

  exists a.
  destruct (Eq_T a a); eauto. omega. destruct n; auto.

  assert (exists t, count multi t > 1).
  apply (IHmulti (remove a uniques)).
  intros.
  assert (s <> a).
  apply In_not_In__not_eq with (xs := multi); eauto.
  assert (count uniques s = 1).
  apply H. eauto.
  rewrite <- remove_ne_no_change; eauto.

  assert (In a uniques). apply count__In.
  assert (count uniques a = 1). eauto. omega.
  assert (length uniques > length (remove a uniques)).
   apply remove_in__dec_count. eauto.
  omega.

  destruct H2. exists x.
  destruct (Eq_T x a). omega. omega.
 Qed.

 Theorem pigeonhole (multi : list T):
   length multi > length Values ->
   exists (t : T), count multi t > 1.
 Proof.
  apply pigeonhole_impl.
  intros.
  apply Includes.
 Qed.


End Finite.

