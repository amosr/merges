(* Is this junk in the standard library? *)

Section Map.
 Variable K : Type.
 Variable V : Type.
 Definition EqDec  := forall (n m : K), { n = m } + { n <> m }.
 Hypothesis EqDec_ : forall (n m : K), { n = m } + { n <> m }.

 Ltac eqdec :=
  unfold EqDec in *; intros n m;
  induction n; induction m;
  try solve [left; congruence];
  try solve [right; congruence].


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

End Map.

