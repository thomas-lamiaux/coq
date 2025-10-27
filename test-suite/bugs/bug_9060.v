Fixpoint plus (n m : nat) : nat.
Proof.
  destruct n.
  - exact m.
  - exact (S (plus n m)).
Qed.
(* with -async-proofs on:
Recursive definition of plus is ill-formed.
In environment ...
Recursive call to plus has principal argument equal to
"m" instead of a subterm of "m".
Recursive definition is: ... *)
