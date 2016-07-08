(* Notes on tactics *)
Require Import Merges.Tactics.LibTactics.

(* false / tryfalse: subsumes all these I think *)
  (* contradict H: proof by not H *)
  (* discriminate: proof by absurd assumption on equality of different constructors *)
  (* exfalso: proof by deriving False *)
Theorem eg_false
  (H: 0 = 1): False.
Proof. false. Qed.

(* destruct_all t: forall (x : t) in context, destruct *)


(* injects t *)
Theorem eg_injects n m
  (H : S (S n) = S m):
    S n = m.
Proof.
 injects~ H.
Qed.


(* Higher-order tactic notation *)
Tactic Notation "!" tactic(t) := t; easy'.
Theorem eg_now (xs : list nat): length xs > 0 -> xs <> nil.
Proof.
  !destruct xs.
Qed.


(* Destruct and remember *)
Theorem eg_destruct_eqn (xs : list nat): length xs > 0 -> xs <> nil.
Proof.
  destruct xs eqn:x.
  (* x : xs = nil *)
  easy.
  (* x : xs = (n :: l) *)
  easy.
Qed.

(* Induct and generalize *)
Theorem eg_induction_in (n m : nat) : n + m = m + n.
Proof.
  induction n in m |- *.
  (* equivalent to 'gen m; induction n; intros.' *)
  (* however only works for single thing *)
  auto.
  simpl. rewrite IHn. auto.
Qed.



(* decompose [and or] H; assumption *)


(* tauto can prove some things auto can't *)
(* intuition E splits the proof tree down to small goals and solves each with E. *)
(* "intuition auto" is better than "auto". *)
(* is "firstorder E" better than "intuition E"? *)


(* iauto := intuition with eauto *)
(* jauto and iauto destruct conjunction hypotheses before running auto.
   jauto also destructs existentials.
   iauto destructs disjunctions, but this can be slow if there are many branches. *)

(* congruence can solve a lot of things on equalities.
   I think it subsumes f_equal etc *)



(* psatz can solve some things omega can't, but requires a tool called csdp *)
(* https://coq.inria.fr/refman/Reference-Manual025.html *)


(* ring and field don't seem to be as powerful as omega, but can be extended to work on arbitrary rings *)
(* https://coq.inria.fr/refman/Reference-Manual028.html *)


(* rewrite, reflexivity, transitivity etc can be generalised to work on relations other than eq *)
(* this is probably useful for dealing with equivalence relations for example equivalence of evaluation *)
(* https://coq.inria.fr/refman/Reference-Manual030.html *)

