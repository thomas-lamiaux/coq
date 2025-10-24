Require ssreflect.

Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Set Universe Polymorphism.
Set Printing Universes.

Declare Scope lean_scope.
Global Open Scope lean_scope.

Cumulative
Inductive eq@{u|} {α:Type@{u}} (a:α) : α -> SProp
  := eq_refl : eq a a.
Notation "x = y" := (eq x y) : lean_scope.

#[export]
Set Implicit Arguments.
Record Iso (A B : Type) : Type := {
    to : A -> B;
}.

Definition rel_iso {A B} (i : Iso A B) : A -> B -> _ := fun x y => i.(to) x = y.

Existing Class Iso.
Import ssreflect.

Inductive Nat := Nat_zero : Nat | Nat_succ : Nat -> Nat.

Instance nat_iso : Iso nat Nat.
Admitted.

Axiom add_comm : forall n m, n + m = m + n.

Definition plus_iso
    :   forall n m,
        rel_iso nat_iso (n + m) Nat_zero.
Proof.
    intros n m.
    rewrite add_comm.
    all: admit.
Defined.
(* Binder (_evar_0_ : "rel_iso@{Set Set} nat_iso (m + n) (nat_iso m)")
has relevance mark set to relevant but was expected to be
irrelevant (maybe a bugged tactic). *)
