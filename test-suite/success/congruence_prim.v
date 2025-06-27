Require Import Corelib.Numbers.Cyclic.Int63.PrimInt63.
Require Import Corelib.Strings.PrimString.
Require Import Corelib.Floats.PrimFloat.

Inductive Box (A : Type) := box : A -> Box A.

Arguments box {A}.

Goal box 0%uint63 = box 1%uint63 -> False.
Proof.
congruence.
Abort.

Goal box "true"%pstring = box "false"%pstring -> False.
Proof.
congruence.
Qed.

Goal box 1.0%float = box 2.0%float -> False.
Proof.
congruence.
Qed.
