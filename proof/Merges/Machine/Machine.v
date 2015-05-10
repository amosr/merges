Require Import Merges.Tactics.
Require Import Merges.Map.

Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.

Section Machine.

 (* ~~~~ Input types ~~~~~~~~ *)
 Record Types
  := mkTypes

  (* The names of input channels *)
  { input       : Type
  (* do we need to see if two are the same? *)
  ; inputEqDec  : EqDec input

  (* The names of output channels.
     I'm not sure whether separating these will make fusion too complicated
     because fusing can remove inputs  *)
  ; output      : Type
  (* do we need to see if two are the same? *)
  ; outputEqDec : EqDec output

  (* Let's start simple with only one value type *)
  ; val         : Type
  (* And we'll assume there is some sort of bottom for uninitialised values.
     This is not ideal, but it makes it simpler to allow worker functions
     access to all values *)
  ; uninitialised : val

  (* State labels *)
  ; label       : Type
  (* We also need an initial label *)
  ; initial     : label

  (* The stateOf : label -> State
     would make sense in here, but State isn't defined yet
     and depends on the types in here *)
  }.

 Variable t : Types.



 (* ~~~~ Definitions ~~~~~~~~ *)

 (* Output channels can have states assigned to them.
    You can also read the last output value. *)
 Inductive Var
   (* Value of last read from channel *)
  := VInput       : input  t -> Var
   (* Value that was last written to channel *)
   | VOutput      : output t -> Var
   (* Output channel's state *)
   | VState       : output t -> Var.

 Theorem VarEqDec : EqDec Var.
  unfold EqDec in *. intros.  
  destruct n; destruct m;
  try destruct (inputEqDec t i i0);
  try destruct (outputEqDec t o o0);
  try solve [left; congruence];
  try solve [right; congruence].
 Qed.

 (* Given a mapping from variables to values, a "worker function" computes a value *)
 Definition Env    := Var -> val t.
 Definition Func a := Env -> a.


 (* Put the labels in the state type so we don't need dependent types or whatever *)
 Inductive State
   (* Pull from an input channel *)
  := Pull    : input t
             (*some*) (*none*)
            -> label t -> label t
            -> State
   (* Release input value *)
   | Release : input t -> label t
            -> State
   (* Close input channel - I promise not to read again *)
   | Close   : input t -> label t
            -> State
   (* Push f(env) to output channel *)
   | Out     : output t
            -> Func  (val t)
            -> label  t
            -> State
   (* Output channel is finished *)
   | OutDone : output t
            -> label  t
            -> State
   (* If f(env) *)
   | If      : Func bool
             (*then*) (*else*)
            -> label t -> label t
            -> State
   (* output's state = f(env) *)
   | Update  : output t
            -> Func  (val t)
            -> label  t
            -> State
   (* Goto*)
   | Skip    : label  t
            -> State
   (* Nothing more to do *)
   | Done    : State.

 (* Finally, each label needs a state *)
 Variable stateOf : label t -> State.




 (* ~~~~ Evaluation ~~~~~~~~ *)

 (* We need some values to start the party *)
 Definition emptyEnv : Env
  := fun _ => uninitialised t.

 (* Each input channel needs a list of values, as does output *)
 Definition Inputs  := input  t -> list (val t).
 Definition Outputs := output t -> list (val t).

 (* Pull from an input *)
 Definition pull (i : input t) (is : Inputs) : (Inputs * option (val t))
  := match is i with
     | [] 
        => (is, None)
     | (x::xs)
        => (update _ _ (inputEqDec t) i xs is, Some x)
     end.


 Theorem pull_decreases:
  forall is i j is' o
   , pull  i is = (is', o)
  -> length (is' j) <= length (is j).
 Proof.
  intros.
  unfold pull in *.

  remember (is i) as inp.

  destruct inp. injects H. eauto.
  injects H.

  destruct (inputEqDec t i j); subst.

  rewrite update_eq_is.
  rewrite <- Heqinp. simpl. eauto.

  rewrite update_ne_is; eauto.
 Qed.

 Theorem pull_strictly_decreases:
  forall is i is' o
   , pull  i is = (is', o)
  -> length (is' i) = length (is i) - 1.
 Proof.
  intros.
  unfold pull in *.

  remember (is i) as inp.

  destruct inp. injects H.
  rewrite <- Heqinp. eauto.

  injects H.
  rewrite update_eq_is.
  simpl. omega.
 Qed.


 (* Initially all outputs are empty *)
 Definition initialOuts : Outputs
  := Map.empty _ _ [].

 (* Push to an output *)
 Definition push (o : output t) (v : val t) (os : Outputs) : Outputs
  := update _ _ (outputEqDec t) o (v :: os o) os.

 
 (* What is a better name? The actual evaluation state of running a machine *)
 Definition STATE := (label t * Inputs * Outputs * Env)%type.

 (* Single-step semantics *)
 Definition run1 (r : STATE) : STATE
  := match r with
     (l, is, os, e)
     => match stateOf l with
        | Pull i lT lF
        => match pull i is with
           | (is', None)
           => (lF, is', os, e)
           | (is', Some v)
           => (lT, is', os, update _ _ VarEqDec (VInput i) v e)
           end

        | Release i l'
        => (l', is, os, e)

        | Close   i l'
        => (l', is, os, e)

        
        | Out o f l'
        => let v   := f e              in
           let os' := push o v os      in
           let e'  := update _ _ VarEqDec (VOutput o) v e
           in (l', is, os', e')

        | OutDone o l'
        => (l', is, os, e)

        
        | If p lT lF
        => if   p e
           then (lT, is, os, e)
           else (lF, is, os, e)
         
        | Update o f l'
        => (l', is, os, update _ _ VarEqDec (VState o) (f e) e)

        | Skip l'
        => (l', is, os, e)
        
        (* I'm not sure about this; should return type be option & return none? *)
        | Done
        => (l, is, os, e)

        end
     end.


 (* We define a sequence of *non-empty* evaluation steps.
    If the machine is done, it can still have a non-empty evaluation sequence.
    But if the machine is not done, a non-empty evaluation sequence must
    actually change something. *)
 Inductive runs : STATE -> STATE -> Prop
 := Run1      : forall s t
              , t = run1 s
             -> runs s t
  | RunN      : forall s s'
              , runs (run1 s) s'
             -> runs s s'.

 (* Execute the whole machine *)
 Inductive exec : Inputs -> Outputs -> Prop
  := Exec     : forall is l' is' os' e'
              , stateOf l' = Done
             -> runs (initial t, is, initialOuts, emptyEnv)
                     (l', is', os', e')
             -> exec is os'.

 (* We want to say that *)
(* Definition simple_decreasing
  := forall is l os e,


 Definition terminates
              := forall is,
              exists os,
              exec is os.


 (* but in order to prove termination of whole program,
    probably need to show for all states *)
 Definition terminates_all_states
              := forall l is os e,
              exists l' is' os' e',
              runs (l, is, os, e) (l', is', os', e').

 (* Termination variant?
    Maybe something about, for each label L, whenever you get back to L
    either lists will be shorter, or some variant on env will be smaller *)
*)
End Machine.
