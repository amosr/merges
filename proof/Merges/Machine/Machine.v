Require Import Merges.Tactics.
Require Import Merges.Map.

Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.

Section Machine.

 (* ~~~~ Definition ~~~~~~~~ *)

 (* The names of input channels *)
 Variable   input       : Type.
 (* do we need to see if two are the same? *)
 Hypothesis inputEqDec  : EqDec input.

 (* The names of output channels.
    I'm not sure whether separating these will make fusion too complicated
    because fusing can remove inputs  *)
 Variable   output      : Type.
 (* do we need to see if two are the same? *)
 Hypothesis outputEqDec : EqDec output.


 (* Let's start simple with only one value type *)
 Variable   val   : Type.
 (* And we'll assume there is some sort of bottom for uninitialised values.
    This is not ideal, but it makes it simpler to allow worker functions
    access to all values *)
 Variable   uninitialised : val.


 (* Output channels can have states assigned to them.
    You can also read the last output value. *)
 Inductive Var
   (* Value of last read from channel *)
  := VInput       : input  -> Var
   (* Value that was last written to channel *)
   | VOutput      : output -> Var
   (* Output channel's state *)
   | VState       : output -> Var.

 Theorem VarEqDec : EqDec Var.
  unfold EqDec in *. intros.  
  destruct n; destruct m;
  try destruct (inputEqDec i i0);
  try destruct (outputEqDec o o0);
  try solve [left; congruence];
  try solve [right; congruence].
 Qed.

 (* Given a mapping from variables to values, a "worker function" computes a value *)
 Definition Env    := Var -> val.
 Definition Func t := Env -> t.


 (* State labels *)
 Variable label : Type.

 (* Put the labels in the state type so we don't need dependent types or whatever *)
 Inductive State
   (* Pull from an input channel *)
  := Pull    : input
             (*some*) (*none*)
            -> label -> label
            -> State
   (* Release input value *)
   | Release : input -> label
            -> State
   (* Close input channel - I promise not to read again *)
   | Close   : input -> label
            -> State
   (* Push f(env) to output channel *)
   | Out     : output
            -> Func val
            -> label
            -> State
   (* Output channel is finished *)
   | OutDone : output
            -> label
            -> State
   (* If f(env) *)
   | If      : Func bool
             (*then*) (*else*)
            -> label -> label
            -> State
   (* output's state = f(env) *)
   | Update  : output
            -> Func val
            -> label
            -> State
   (* Goto*)
   | Skip    : label
            -> State
   (* Nothing more to do *)
   | Done    : State.

 (* We need an initial label *)
 Variable initial : label.

 (* And each label needs a state *)
 Variable stateOf : label -> State.



 (* ~~~~ Evaluation ~~~~~~~~ *)

 (* We need some values to start the party *)
 Definition emptyEnv : Env
  := fun _ => uninitialised.

 (* Each input channel needs a list of values, as does output *)
 Definition Inputs  := input  -> list val.
 Definition Outputs := output -> list val.

 (* Pull from an input *)
 Definition pull (i : input) (is : Inputs) : (Inputs * option val)
  := match is i with
     | [] 
        => (is, None)
     | (x::xs)
        => (update _ _ inputEqDec i xs is, Some x)
     end.

 (* Initially all outputs are empty *)
 Definition initialOuts : Outputs
  := Map.empty _ _ [].

 (* Push to an output *)
 Definition push (o : output) (v : val) (os : Outputs) : Outputs
  := update _ _ outputEqDec o (v :: os o) os.

 Definition STATE := (label * Inputs * Outputs * Env)%type.

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

        | Done
        => (l, is, os, e)

        end
     end.


 Inductive runs : STATE -> STATE -> Type
 := RunDone   : forall l is os e
              , stateOf l = Done
             -> runs (l,is,os,e) (l,is,os,e)
  | Run1      : forall s s'
              , runs (run1 s) s'
             -> runs s s'.

 Inductive exec : Inputs -> Outputs -> Type
  := Exec     : forall is l' is' os' e'
              , runs (initial, is, initialOuts, emptyEnv)
                     (l', is', os', e')
             -> exec is os'.

End Machine.
