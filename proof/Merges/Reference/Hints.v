(* What do hints do? *)
Require Import Merges.Tactics.LibTactics.



Module Hints.
  Inductive Even : nat -> Prop := 
   | Even_0 : Even 0
   | Even_SS n : Even n -> Even (S (S n)).
  Hint Constructors Even.

  Theorem even_zero: Even 0.
  Proof.
   (* Hint Constructors can solve this *)
   auto.
  Qed.
  Theorem even_suc n: Even n \/ Even (S n).
   (* Hint Constructors solves the leaves fine, too *)
   induction n; auto; destruct IHn; auto.
  Qed.

  Hint Resolve even_suc.
  Theorem even_suc2 n: Even n \/ Even (S n).
   (* Hint Resolve changes this to an 'apply even_suc' *)
   auto.
  Qed.


  Definition double n : nat := n * 2.
  Hint Unfold double.
  Theorem even_double n: Even n -> Even (double n).
  Proof.
    intros; induction H; unfold double; simpl; auto.
    (* The Unfold hint doesn't do anything here, since we need
       simplification between unfolding and auto.
       Is there a way around this? *)
  Qed.



  Hint Extern 1 (Even (double (S _))) => (unfold double; simpl)
    : cheat_db_1.
  Theorem even_double_db_1 n: Even n -> Even (double n).
  Proof.
    intros; induction H; auto with cheat_db_1.
    (* This will do it, but it's too specific to be useful *)
  Qed.


  Ltac unfold_simp_double :=
    match goal with
    | |- _ (double _) => unfold double; simpl
    end.
  Hint Extern 1 => (unfold_simp_double)
    : cheat_db_2.

  Theorem even_double_db_2 n: Even n -> Even (double n).
  Proof.
    intros; induction H; auto with cheat_db_2.
    (* This works, but is still a bit unwieldy. Can it be abstracted? *)
  Qed.


  Ltac unfold_simp F :=
    match goal with
    | |- context [F _] => unfold F; simpl
    end.
  Hint Extern 1 => (unfold_simp double)
    : cheat_db_3.

  Theorem even_double_db_3 n: Even n -> Even (double n).
  Proof.
    intros; induction H; auto with cheat_db_3.
    (* This is about as good as we'll get. I wonder whether
       these 'unindexed hints' will slow down general proofs much. *)
  Qed.


  Hint Extern 1 => simpl
    : cheat_db_4.

  Theorem even_double_db_4 n: Even n -> Even (double n).
  Proof.
    intros; induction H; auto with cheat_db_4.
    (* This does not work at all *)
    unfold double; simpl; auto.
  Qed.


  Theorem double_rewrite n: double n = n * 2.
  Proof. auto. Qed.
  Hint Rewrite double_rewrite : cheat_db_5.
  Theorem even_double_db_5 n: Even n -> Even (double n).
  Proof.
    intros; induction H; autorewrite with cheat_db_5 in *.
    (* The rewrite happens, but no simp.
       But we can use the auto db with 'simpl' as well. *)
    all: auto with cheat_db_4.
  Qed.


  Theorem even_double_db_6 n: Even n -> Even (double n).
  Proof with auto with cheat_db_3.
    intros H; induction H...
    (* I guess this is the winner *)
  Qed.
End Hints.
