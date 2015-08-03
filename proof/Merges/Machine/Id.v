Require Import Merges.Machine.Machine.
Require Import Merges.Map.

(* It's actually somewhat nicer without this.
   Seems that inference for record values isn't so good. *)
(* Set Implicit Arguments. *)

Require Import Merges.List.List.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Program.Equality.

Require Import Merges.Tactics.

(* Let's define a simple machine *)


(* With one input *)
Inductive Input := Input_.

Theorem InputEqDec : EqDec Input.
Proof.
 unfold EqDec.
 intros.
 destruct n; destruct m; eauto.
Qed.

(* And one output *)
Inductive Output := Output_.

Theorem OutputEqDec : EqDec Output.
 unfold EqDec.
 intros.
 destruct n; destruct m; eauto.
Qed.

(* Which only works over nats *)
Definition val := nat.
Definition uninitialised : val := 0.

(* And has three states *)
Inductive Label
 := L0 | L1 | L2.

Definition IdTypes
 := mkTypes
    InputEqDec
    OutputEqDec
    uninitialised
    L0.

(* Repeatedly pull from input, writing to output *)
Definition stateOf (l : Label) : State IdTypes
 := match l with
    | L0 => Pull IdTypes Input_  L1 L2
    | L1 => @Out IdTypes Output_ (fun e => e (VInput IdTypes Input_)) L0
    | L2 => Done IdTypes
    end.

Definition lengthOfState (s : STATE IdTypes)
 := match s with
   | (_, is, _, _) => length (is Input_)
  end.

Lemma all_nonincreasing:
  forall s s'
    (r :  @runs IdTypes stateOf s s'),
  runs_all_nonincreasing lengthOfState r.
Proof.
 intros.
 induction r; simpl; state_destruct.
 sapply* state_maybe_decreasing.
 split~.
 sapply* state_maybe_decreasing.
Qed.

(* if we can get from L back to L, something must be smaller *)
Definition loop_decreasing
 := forall l is os e is' os' e',
  @runs IdTypes stateOf (l, is, os, e) (l, is', os', e')
  -> forall i, length (is' i) < length (is i).


(* Does it terminate for all states? *)
(*
Lemma termination_all: @terminates_all_states IdTypes stateOf.
Proof.
 unfold terminates_all_states.
 intros.
 repeat eexists.
 destruct l.
 eapply Exec.
 simpl.
 apply Run1.
 constructor.
 eauto.
*)
(*Theorem Exec: forall (inp : list nat) (os : Outputs Output nat),
    exec InputEqDec OutputEqDec 0 L0 stateOf (fun _ => inp) os
 -> os Output_ = reverse inp.
Proof.
 intros.
 inductions' H.
 inductions' r.

 assert (l = L0) by congruence.
 rewrite H in *.
 inversion e0.
 subst.

 gen_eq H.
 generalize.
 dependent destruction H.

 dependent induction r.
 eauto.
 induction H.
*)
