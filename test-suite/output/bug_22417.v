(* Recursive occurrences in fixpoint binder types must report an error, not an anomaly. *)
Fail Fixpoint annotation_loop : nat -> nat :=
  fun n : (let unused := annotation_loop 0 in nat) => n.
