(* -*- coq-prog-args: ("-async-proofs" "on"); -*- *)

Definition dummy := tt.

Definition delayed_abstract : unit.
Proof.
abstract constructor.
Qed.
