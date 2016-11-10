(*
  Ltac destruct_apps_2 FUN :=
  match goal with
  | [ _ : context [ FUN ?a ?b ] |- _ ]
  => let x := fresh "destruct_" FUN in remember (FUN a b) as x
     ; destruct x
     ;  repeat match goal with
       | [ H : _ = FUN a b |- _ ] => gen H
       end
  end.
  Tactic Notation "destruct_apps_3" tactic(FUN) :=
  match goal with
  | [ _ : context [ FUN ?a ?b ] |- _ ]
  => let x := fresh "destruct_" FUN in remember (FUN a b) as x
     ; destruct x
     ;  repeat match goal with
       | [ H : _ = FUN a b |- _ ] => gen H
       end
  end.
  (* neither of these work: 
      destruct_apps_3 P.StreamType.
      destruct_apps_2 P.StreamType.
    and this doesn't work either
      destruct_apps (P.StreamType P2).
  *)
*)