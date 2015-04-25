Require Import Merges.Machine.Machine.
Require Import Merges.Map.
Set Implicit Arguments.

Require Import Merges.List.List.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Program.Equality.

Require Import Merges.Tactics.

Inductive Input := Input_.
Theorem InputEqDec : EqDec Input.
 unfold EqDec.
 intros.
 destruct n; destruct m; eauto.
Qed.

Inductive Output := Output_.
Theorem OutputEqDec : EqDec Output.
 unfold EqDec.
 intros.
 destruct n; destruct m; eauto.
Qed.

Definition Val := nat.

Inductive Label
 := L0 | L1 | L2.

Definition stateOf (l : Label) : State Input Output Val Label
 := match l with
    | L0 => Pull _ _ Input_  L1 L2
    | L1 => Out  Output_ (fun e => e (VInput _ Input_)) L0
    | L2 => Done _ _ _ _
    end.

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
