Require Import Merges.Tactics.
Require Import Merges.Map.

Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.


Module DFA.
Section DFA.

  Variable Label : Set.
  Variable Alphabet : Set.

  Variable Init : Label.
  Variable Done : Label -> Prop.
  Variable Step : Label -> Alphabet -> Label.

  Fixpoint StepN (i : Label) (ss : list Alphabet) : Label :=
    match ss with
    | [] => i
    | s :: ss => StepN (Step i s) ss
    end.
End DFA.

End DFA.

Record DFA (Alphabet : Set) : Type
  := mkDFA
   { Label : Set
   ; Init : Label
   ; Done : Label -> Prop
   ; Step : Label -> Alphabet -> Label
   }.


Fixpoint StepN {A} (d : DFA A) (i : Label d) (ss : list A) : Label d :=
  match ss with
  | [] => i
  | s :: ss => StepN d (Step d i s) ss
  end.

Definition Accept {A} (d : DFA A) (ss : list A) : Prop :=
 Done d (StepN d (Init d) ss).
Hint Unfold Accept.

Module Synchronous.
Section Synchronous.
 Variable A  : Set.

 Variable M1 : DFA A.
 Variable M2 : DFA A.

 Definition L : Set := Label M1 * Label M2.
 
 Definition Init' := (Init M1, Init M2).
 
 Definition Done' (l : L) :=
  match l with
  | (l1, l2) => Done M1 l1 /\ Done M2 l2
  end.

 Definition Step' (l : L) (a : A) :=
  match l with
  | (l1, l2) => (Step M1 l1 a, Step M2 l2 a)
  end.

 Definition M : DFA A := @mkDFA A L Init' Done' Step'.

 Theorem correspondence s i1 i2
  : Step M (i1,i2) s = (Step M1 i1 s, Step M2 i2 s).
 Proof.
  eauto.
 Qed.

 Theorem correspondence' s i1 i2
  : StepN M (i1,i2) s = (StepN M1 i1 s, StepN M2 i2 s).
 Proof.
  gen i1 i2.
  !induction s; intros; !simpls.
 Qed.

 Theorem accept s : Accept M s <-> Accept M1 s /\ Accept M2 s.
 Proof.
  simpls.
  unfold Init'.
  rewrite correspondence'.
  simpls.
  !split.
 Qed.
End Synchronous.
End Synchronous.

Module Synchronised.
Section Synchronised.
 Variable A1 : Set.
 Variable A2 : Set.

 Variable A  : Set.

 Variable A1X : A -> option A1.
 Variable A2X : A -> option A2.

 Variable M1 : DFA A1.
 Variable M2 : DFA A2.

 Definition L : Set := Label M1 * Label M2.

 Definition Init' := (Init M1, Init M2).

 Definition Done' (l : L) :=
  match l with
  | (l1, l2) => Done M1 l1 /\ Done M2 l2
  end.

 Definition Step' (l : L) (a : A) :=
  match l, A1X a, A2X a with
  | (l1, l2), None   , None    => (l1, l2)
  | (l1, l2), None   , Some a2 => (l1, Step M2 l2 a2)
  | (l1, l2), Some a1, None    => (Step M1 l1 a1, l2)
  | (l1, l2), Some a1, Some a2 => (Step M1 l1 a1, Step M2 l2 a2)
  end.

 Definition M : DFA A := @mkDFA A L Init' Done' Step'.

 Fixpoint filterA1 (ss : list A) : list A1 :=
  match ss with
  | [] => []
  | a :: ss
  => match A1X a with
     | None    =>       filterA1 ss
     | Some a1 => a1 :: filterA1 ss
     end
  end.

 Fixpoint filterA2 (ss : list A) : list A2 :=
  match ss with
  | [] => []
  | a :: ss
  => match A2X a with
     | None    =>       filterA2 ss
     | Some a2 => a2 :: filterA2 ss
     end
  end.

 Theorem correspondence' s i1 i2
  : StepN M (i1,i2) s = (StepN M1 i1 (filterA1 s), StepN M2 i2 (filterA2 s)).
 Proof.
  gen i1 i2.
  !induction s; intros; simpls; destruct (A1X a); !destruct (A2X a).
 Qed.

 Theorem accept s
  : Accept M s <-> Accept M1 (filterA1 s) /\ Accept M2 (filterA2 s).
 Proof.
  simpls.
  unfold Init'.
  rewrite correspondence'.
  simpls.
  !split.
 Qed.

End Synchronised.
End Synchronised.

