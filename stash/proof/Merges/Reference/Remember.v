Require Import Merges.Tactics.LibTactics.


Module Records.
  Require Import Coq.Program.Tactics.

  Record var  := { v : Set; eqdec : (forall (n m : v), {n = m} + {n <> m}) }.

  Program Definition var_nat := {| v := nat |}.
  Next Obligation.
    decides_equality.
  Qed.

End Records.


Module ImplicitNames.
  Implicit Types m n : nat.
  Function plus m n :=
   match n with
   | 0 => m
   | S n' => S (plus m n')
   end.
End ImplicitNames.


Module Generalize.
  Generalizable All Variables.

  Definition id `(x : A) : A := x.
  Definition fmap `(f : A -> B) (xs : list A) : list B := nil.

  Lemma nat_comm : `(n = n + 0). eauto. Qed.

End Generalize.


(* Program derivation *)
Module Derive.
  Section fmap_list.
    Require Coq.derive.Derive.

    Variables (A B : Set) (f : A -> B) (xs : list A).
    (* This is not actually deriving a correct fmap. *)
    Derive fmap SuchThat (length fmap = length xs) As H.

    Proof.
      (* These are not necessary *)
      Show Existentials.
      instantiate (1 := A).

      subst fmap. reflexivity.
    Defined.

  End fmap_list.
End Derive.


Module Dependent.
  Require Import Coq.Program.Equality.

  Theorem eq_is_eq (A : Set) (n m : A) (a b : n = m):
    a = b.
  Proof.
    dependent destruction a.
    dependent destruction b.
    eauto.
  Qed.
End Dependent.


Module FunExt.
  Require Import Coq.Logic.FunctionalExtensionality.

  Theorem falsy_eq (A : Set) (a b : A -> False):
    a = b.
  Proof.
    extensionality x.
    destruct (a x).
  Qed.
End FunExt.


Module GoalSelector.
  Set Default Goal Selector "all".

  Theorem splits: 1 = 1 /\ 2 = 2 /\ 3 = 3.
  Proof.
   splits.
   reflexivity.
   (* Might be easier to debug than nested semicolons *)
  Qed.
End GoalSelector.


Module Quoted.
  Require Import Quote.
  Inductive num : Set :=
   | num_plus  : num -> num -> num
   | num_const : nat -> num
   | num_atom  : Quote.index -> num.

  Fixpoint eval (vm : Quote.varmap nat) (n : num) : nat :=
   match n with
   | num_plus a b => eval vm a + eval vm b
   | num_const a  => a
   | num_atom i   => Quote.varmap_find 0 i vm
   end.
  

  Theorem adds (vm : Quote.varmap nat) (a b : num)
    : eval vm (num_plus a b) = eval vm a + eval vm b.
  Proof.
   set (eval vm a + eval vm b) as x.
   quote eval in (eval vm a + eval vm b) using (fun y => assert (x = y)).
   simpl. auto.
   auto.
   (* This is incredibly stupid and convoluted since 'auto' solves it fine. *)
  Qed.
End Quoted.


Module DependentMatch.
  Inductive Vec (A : Set) : nat -> Set :=
    | v_nil : Vec A 0
    | v_cons (a : A) (n : nat) : Vec A n -> Vec A (S n).

  (* I don't think earlier versions were smart enough to figure this out *)
  Definition head {A : Set} {n : nat} (v : Vec A (S n)) : A :=
    match v with
    | v_cons _ a _ _ => a
    end.

  (* The above desugars to something like: *)
  Definition head_explicit {A : Set} {n : nat} (v : Vec A (S n)) : A :=
    match v
      (* This is the type of the scrutinee, and binds 'n0' in the return clause *)
      in (Vec _ n0)
      (* So this is matching on the length of the scrutinee vector *)
      return
        match n0 with
        (* If it is zero, just return unit. *)
        | 0 => unit
        (* For all other cases we can return an A *)
        | _ => A
        end
    with
    (* The actual clauses are standard, except nil returns unit *)
    | v_nil _ => tt
    | v_cons _ a _ _ => a
    end.

  (* But append can't be synthesised without some help *)
  Fixpoint vec_app {A : Set} {n m : nat} (v : Vec A n) (u : Vec A m) : Vec A (n + m) :=
  match v
    (* This 'n0' is different from 'n', even though they should be the same *)
    in (Vec _ n0)
    (* So this has to be 'n0' and does not work if it's 'n'. Isn't that weird? *)
    return (Vec _ (n0 + m))
  with
  (* The clauses are the same though *)
  | v_nil _ => u
  | v_cons _ a _ v' => v_cons _ a _ (vec_app v' u)
  end.

  (* Zipping is very hard to write without 'Program' to synthesise the equalities *)
  Program Fixpoint vec_zip {A B : Set} {n : nat} (v : Vec A n) (u : Vec B n) : Vec (A * B) n :=
  match v in Vec _ n0,
        u in Vec _ n1
    (* Somehow we lost the fact that the lengths are the same,
       so add it as a hypothesis *)
    return n0 = n1 -> Vec _ n0
  with
  (* Both nil is easy *)
  | v_nil _, v_nil _
      => fun _
      => v_nil _
  (* Both cons will use the length equality to rewrite *)
  | v_cons _ a _ v', v_cons _ b _ u'
      => fun _
      => v_cons _ (a,b) _ (vec_zip v' u')
  (* This will end up destructing False or something *)
  | _, _
      => _
  end eq_refl.

End DependentMatch.

Module Programs.
  Require Import Coq.Program.Tactics.
  Require Import Coq.Program.Program.
  Require Import Omega.

  Program Definition subInject (x : nat) : { y : nat | y = S x }
    := S x.

  Program Definition subProject (x : nat) : nat := subInject x.

  Program Fixpoint div2 (n : nat) : { x : nat | n = 2 * x \/ n = 2 * x + 1 } :=
        match n with
        | S (S p) => S (div2 p)
        | _ => O
        end.
  (* Why doesn't this do anything? *)
  (* Solve Obligations with omega. *)
  Next Obligation. omega. Defined.
  Next Obligation.
   destruct n; auto.
   destruct n; auto.
   destruct (H n); auto.
  Defined.
End Programs.

