(* Is this junk in the standard library? *)

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

End Map.

