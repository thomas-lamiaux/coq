
Require Import Ltac2.Ltac2.

Module B13462.

  Axiom plus: nat -> nat -> nat.

  Declare Custom Entry foo.

  Definition enter{T: Type}: T -> T := @id T.

  Notation "a +++ b" := (plus a b) (in custom foo at level 5, a custom foo, b custom foo).
  Notation "x" := x (in custom foo at level 0, x ident).
  Notation "{{ x }}" := (enter x) (x custom foo at level 5).

  Ltac2 Notation "go" "(" a(constr(custom(foo))) ")" := pose $a as x.

  Goal forall (p q: nat), False.
  Proof.
    intros.
    go (p +++ q).
  Abort.

End B13462.

Declare Custom Entry bar.

Fail Ltac2 Notation "foo" a(constr(custom(foo))) := a.
Succeed Ltac2 Notation "foo" a(constr(custom(B13462.foo))) := a.

Fail Ltac2 Notation "foo" a(constr(custom(foo,bar))) := a.

Fail Ltac2 Notation "foo" a(constr(level(-10))) := a.
Fail Ltac2 Notation "foo" a(constr(level(bar))) := a.

Ltac2 Notation "foo" a(constr(level(10))) := a.
Ltac2 Eval foo S 0.
Ltac2 Eval (foo S : constr). (* ": constr" is a ltac2 cast not a term cast *)

Fail Ltac2 Notation "bar" a(constr(level(10),level(10))) := a.
Ltac2 Notation "bar" a(constr(custom(bar),level(0))) "!" := a.
Ltac2 Notation "bar" a(constr) "!" := a.

Notation "!! x" := (S x : bool) (in custom bar at level 10, x custom bar at level 0).
Notation "##" := (0:bool) (in custom bar).

Notation "!! x" := (S x) (at level 2).

Ltac2 Eval bar !! 0 !. (* picked bar with argument in constr so succeeds *)
Fail Ltac2 Eval bar ## !. (* picked bar with argument in custom bar so fails (nat <> bool) *)
