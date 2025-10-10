Ltac foo H := idtac H.
Goal True.
Proof.
  Fail foo.
(* Error: An unnamed user-defined tactic was not fully applied:
There is a missing argument for variable H, no arguments at all were provided. *)
Abort.
