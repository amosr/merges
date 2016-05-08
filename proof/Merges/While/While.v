Require Import Merges.Tactics.
Require Import Merges.Map.


Require Import Merges.List.List.
Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.

Module Type While.
 Variable Stream : Set.
 Variable Scalar : Set.
 Variable Value  : Set.

 Variable StreamEqDec : EqDec Stream.
 Variable ScalarEqDec : EqDec Scalar.
End While.

Module Program (W : While).
 Definition Heap := Map W.Scalar W.Value.
 Definition Exp  := Heap -> W.Value.
 Definition Pred := Heap -> bool.
 Definition StreamHeap := Map W.Stream (list W.Value).


 (* Pull from an input *)
 Definition streamPull (i : W.Stream) (is : StreamHeap) : (StreamHeap * option W.Value)
  := match is i with
     | [] 
        => (is, None)
     | (x::xs)
        => (update _ _ W.StreamEqDec i xs is, Some x)
     end.

 (* Push to an output *)
 Definition streamPush (o : W.Stream) (v : W.Value) (os : StreamHeap) : StreamHeap
  := update _ _ W.StreamEqDec o (v :: os o) os.

 (* Push to an output *)
 Definition scalarWrite (n : W.Scalar) (v : W.Value) (h : Heap) : Heap
  := update _ _ W.ScalarEqDec n v h.


 Inductive Program
  := Skip  : Program
   | Push  : W.Stream -> Exp -> Program
   | Pull  : W.Scalar -> W.Stream -> Program -> Program
   | Write : W.Scalar -> Exp -> Program
   | While : Pred -> Program -> Program
   | Semicolon : Program -> Program -> Program.

 Notation "a ';' b" := (Semicolon a b) (at level 20).

 Inductive Exec (h : Heap) (sh : StreamHeap) : Program -> Heap -> StreamHeap -> Prop
  := ESkip : Exec h sh Skip h sh
   | EPush : forall s v,
             Exec h sh
                 (Push s v)
                  h (streamPush s (v h) sh)

   | EPullNone : forall n s p sh',
             streamPull s sh = (sh', None) ->
             Exec h sh
                 (Pull n s p)
                  h sh'
   | EPullSome : forall n s p sh' v h'' sh'',
             streamPull s sh = (sh', Some v) ->
             Exec (scalarWrite n v h) sh' p h'' sh'' ->
             Exec h sh
                 (Pull n s p)
                  h'' sh''

   | EWrite : forall n x,
             Exec h sh
                 (Write n x) 
                  (scalarWrite n (x h) h) sh

   | EWhileDone : forall pred prog,
             pred h = false ->
             Exec h sh
                 (While pred prog)
                  h sh
   | EWhileGo : forall pred prog h' sh' h'' sh'',
             pred h = true ->
             Exec h sh prog h' sh' ->
             Exec h' sh'
                 (While pred prog)
                  h'' sh'' ->
             Exec h sh
                 (While pred prog)
                  h'' sh''

   | ESemicolon : forall p1 p2 h' sh' h'' sh'',
             Exec h sh   p1 h' sh' ->
             Exec h' sh' p2 h'' sh'' ->
             Exec h sh
                 (Semicolon p1 p2)
                  h'' sh''
   .


 Theorem Exec_deterministic p:
  forall h sh h' sh' h'' sh'',
  Exec h sh p h'  sh'  ->
  Exec h sh p h'' sh'' ->
  h' = h'' /\
  sh' = sh''.
 Proof.
  intros.
  gen h'' sh''.
  induction H; intros;
   try solve [inverts H0; best_bet].

  inverts H0; rewrite H in *.

  injects H6; best_bet.
  inverts H6.

  inverts H1; rewrite H in *.
  inverts H7.
  injects H7; best_bet.

  inverts H2.
  rewrite H in *; inverts H7.

  assert (h' = h'0 /\ sh' = sh'0).
  apply IHExec1. assumption.
  inverts H2.
  apply IHExec2. assumption.
  
  inverts H1.
  assert (h' = h'0 /\ sh' = sh'0).
  apply IHExec1. assumption.
  inverts H1.
  apply IHExec2. assumption.
 Qed.

End Program.




Module Drain <: While.
 Inductive Stream' := StreamIn.
 Definition Stream := Stream'.
 Inductive Scalar' := ScalarDone.
 Definition Scalar := Scalar'.
 Definition Value  := nat.
 Definition StreamEqDec : EqDec Stream.
  unfold EqDec.
  intros.
  destruct n; destruct m; eauto.
 Qed.

 Definition ScalarEqDec : EqDec Scalar.
  unfold EqDec.
  intros.
  destruct n; destruct m; eauto.
 Qed.
End Drain.

Module Drain'.
 Module Program' := Program Drain.
 Import Program'.
 Import Drain.

 Notation "! p" := (fun _ => p) (at level 0).

 Definition P
  := Write ScalarDone !0;
     While (fun h => beq_nat (h ScalarDone) 0)
     ( Write ScalarDone !1;
       Pull ScalarDone StreamIn
       ( Write ScalarDone !0)).

 Lemma write_same i s:
  scalarWrite ScalarDone i s = (fun _ => i).
 Proof.
  apply MapExtensional.
  destruct k.
  unfold scalarWrite.
  apply update_eq_is.
 Qed.

 Lemma update_same i s:
  (update Stream (list Value) StreamEqDec StreamIn i s) = (fun _ => i).
 Proof.
  apply MapExtensional.
  destruct k. apply update_eq_is.
 Qed.

 Lemma runs (l : list nat):
  Exec (fun _ => 0) (fun _ => l) P
       (fun _ => 1) (fun _ => []).
 Proof.
  unfold P.
  econstructor. econstructor.

  induction l.
  eapply EWhileGo.

  unfold scalarWrite; rewrite update_eq_is; best_bet.

  econstructor; econstructor.
  unfold streamPull.
  eauto.
  rewrite write_same.
  eapply EWhileDone. simpl. eauto.

  eapply EWhileGo.
  rewrite write_same. eauto.
  econstructor.
  econstructor.
  eapply EPullSome.
  unfold streamPull; eauto.
  rewrite write_same.
  econstructor.
  simpl.
  rewrite write_same in *.
  rewrite update_same in *.
  apply IHl.
 Qed.

End Drain'.



Module Id <: While.
 Inductive Stream' := StreamIn | StreamOut.
 Definition Stream := Stream'.
 Inductive Scalar' := ScalarDone.
 Definition Scalar := Scalar'.
 Definition Value  := nat.
 Definition StreamEqDec : EqDec Stream.
  unfold EqDec.
  intros.
  destruct n; destruct m; eauto.
  right. intros ne. inverts ne.
  right. intros ne. inverts ne.
 Qed.

 Definition ScalarEqDec : EqDec Scalar.
  unfold EqDec.
  intros.
  destruct n; destruct m; eauto.
 Qed.
End Id.

Module Id'.
 Module Program' := Program Id.
 Import Program'.
 Import Id.

 Notation "! p" := (fun _ => p) (at level 0).

 Definition Loop
  := While (fun h => beq_nat (h ScalarDone) 0)
     ( Write ScalarDone !1;
       Pull ScalarDone StreamIn
       ( Push StreamOut (fun h => h ScalarDone);
         Write ScalarDone !0)).

 Definition P
  := Write ScalarDone !0; Loop.

 Definition initList k (l : list Value)
  := update _ _ StreamEqDec k l (fun _ => []).

 Lemma runLoop: forall h sh,
  h ScalarDone = 0 ->
  Exec h sh Loop
       (update _ _ ScalarEqDec ScalarDone 1 h)
       (update _ _ StreamEqDec StreamIn []
       (update _ _ StreamEqDec StreamOut (reverse (sh StreamIn) ++ sh StreamOut) sh)).
 Proof.
  unfold Loop.
  intros.
  remember (sh StreamIn) as l.
  gen h sh.
  induction l; intros.
  - eapply EWhileGo.
    + eauto.
    + econstructor. econstructor.
      simpl.
      eapply EPullNone.
      unfold streamPull. rewrite <- Heql. eauto.
    + assert ((scalarWrite ScalarDone 1 h) = (update Scalar nat ScalarEqDec ScalarDone 1 h)).
      eauto.
      rewrite <- H0.
      assert (sh = (update Stream (list Value) StreamEqDec StreamIn []
     (update Stream (list Value) StreamEqDec StreamOut
        (reverse [] ++ sh StreamOut) sh))).
      simpl.
      apply MapExtensional.
      unfold update. intros.
            destroy_eqdecs StreamEqDec; best_bet.
      rewrite <- H1.
      eapply EWhileDone.
       unfold scalarWrite.
       rewrite update_eq_is. eauto.
  - eapply EWhileGo; eauto.
    + clear IHl.
      econstructor. econstructor.
      eapply EPullSome.
      unfold streamPull.
      rewrite <- Heql.
      eauto.
      repeat econstructor.
    + simpl.
      assert ((scalarWrite ScalarDone 0 (scalarWrite ScalarDone a (scalarWrite ScalarDone 1 h))) = h) as hRw.
       unfold scalarWrite. unfold update.
       apply MapExtensional.
       intros. destroy_eqdecs ScalarEqDec; best_bet.
      rewrite hRw.
      remember ((streamPush StreamOut
                (scalarWrite ScalarDone a (scalarWrite ScalarDone 1 h) ScalarDone)
                (update Stream (list Value) StreamEqDec StreamIn l sh))) as sh1.
      assert ((update Stream (list Value) StreamEqDec StreamIn []
     (update Stream (list Value) StreamEqDec StreamOut
        ((reverse l ++ [a]) ++ sh StreamOut) sh)
         = (update Stream (list Value) StreamEqDec StreamIn []
           (update Stream (list Value) StreamEqDec StreamOut
              (reverse l ++ sh1 StreamOut) sh1)))).
      
      rewrite Heqsh1.
      apply MapExtensional.
      intros.
      unfold scalarWrite. unfold streamPush. unfold update.
      destroy_eqdecs StreamEqDec; best_bet.
      simpl. destroy_eqdecs ScalarEqDec.
      simpl. rewrite <- app_assoc. eauto.

     rewrite H0.
     eapply IHl; best_bet.
     
     rewrite Heqsh1.
     unfold streamPush.
     unfold update.
     destroy_eqdecs StreamEqDec; best_bet.
 Qed.

 Lemma runP (l : list nat):
  Exec (fun _ => 0) (initList StreamIn l) P
       (fun _ => 1) (initList StreamOut (reverse l)).
 Proof.
  unfold P.
  econstructor. econstructor.
  simpl.
  cutrewrite (scalarWrite ScalarDone 0 !(0) = !0).
  remember !0 as h.
  remember (initList StreamIn l) as sh.
  cutrewrite ((initList StreamOut (reverse l)) = 
              (update Stream (list Value) StreamEqDec StreamIn []
       (update Stream (list Value) StreamEqDec StreamOut
          (reverse (sh StreamIn) ++ sh StreamOut) sh))).
  cutrewrite (!1 = update Scalar nat ScalarEqDec ScalarDone 1 h).
  apply runLoop.
   rewrite~ Heqh.
   apply MapExtensional.
   intros. unfold update. destroy_eqdecs ScalarEqDec; best_bet.
   destruct k. destruct n. eauto.
   
  apply MapExtensional.
   intros.
   rewrite Heqsh.
   unfold initList. unfold update.  destroy_eqdecs StreamEqDec; best_bet.
   apply app_nil_end.

  apply MapExtensional.
   intros.
   unfold scalarWrite.
   unfold update.
   destroy_eqdecs ScalarEqDec; best_bet.
 Qed.

End Id'.


 


(*

 Theorem exec_always h sh p:
  exists h' sh',
  Exec h sh p h' sh'.
 Proof.
  gen h sh.
  induction p; intros; try solve [eexists; eexists; econstructor].

  - remember (streamPull s0 sh) as pull.
    destruct pull as [sh' o]; destruct o.
    + destruct (IHp (scalarWrite s v h) sh').
      destruct H.
      eexists; eexists; eapply EPullSome; best_bet.
    + edestruct IHp.
      edestruct H.
      eexists; eexists; eapply EPullNone; best_bet.

  - remember (p h) as pred.
    destruct pred.
    + eexists. eexists. eapply EWhileGo. eauto.
*)
