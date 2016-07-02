(* Is this junk in the standard library? *)
Require Import Merges.Tactics.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.

Section Map.
 Variable K : Type.
 Variable V : Type.
 Definition EqDec  := forall (n m : K), { n = m } + { n <> m }.
 Hypothesis EqDec_ : EqDec.

 Theorem eq_is_eq (A : Set) (n m : A) (a b : n = m):
    a = b.
 Proof.
  dependent destruction a.
  dependent destruction b.
  eauto.
 Qed.

 Theorem falsy_eq (A : Set) (a b : A -> False):
    a = b.
 Proof.
  extensionality x.
  destruct (a x).
 Qed.


 Theorem EqDec_Eq (a b : EqDec) (n m : K):
   a n m = b n m.
 Proof.
  destruct (a n m).
  rewrite e. clear.
  destruct (b m m); bye_not_eq.
  dependent destruction e; eauto.

  destruct (b n m); bye_not_eq.
  unfold not in *.
  cuts_rewrite (n0 = n1); eauto.
  apply falsy_eq.
 Qed.


 Definition Map := K -> V.

 Definition empty (v : V) : Map
  := fun k => v.

 Definition update (k : K) (v : V) (m : Map) : Map
  := fun k' =>
       if EqDec_ k k'
       then v
       else m k'.


 Lemma update_eq_is k v m:
       update k v m k = v.
 Proof.
  unfold update.
  destruct EqDec_; eauto.
  destruct n; eauto.
 Qed.

 Lemma update_ne_is k v m k':
       k <> k'
    -> update k v m k' = m k'.
 Proof.
  intros.
  unfold update.
  destruct EqDec_; eauto.
  destruct H; eauto.
 Qed.

 Axiom MapExtensional : forall (m m' : Map),
   (forall k, m k = m' k) ->
   m = m'.


End Map.

Ltac prove_eqdec
 := unfold EqDec; intros n m; induction n; destruct m; eauto;
      try solve [right; intros not; inversion not].

Ltac destroy_eqdecs EQDEC
 := repeat destruct EQDEC; bye_not_eq.
