(* Is this junk in the standard library? *)
Require Import Merges.Tactics.Stuff.

Section Map.
 Variable K : Type.
 Variable V : Type.
 Definition EqDec  := forall (n m : K), { n = m } + { n <> m }.
 Hypothesis EqDec_ : forall (n m : K), { n = m } + { n <> m }.


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


Ltac destroy_eqdecs EQDEC
 := repeat destruct EQDEC; bye_not_eq.
