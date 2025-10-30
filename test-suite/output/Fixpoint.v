Require Import ListDef.

Check
  (fix F (A B : Set) (f : A -> B) (l : list A) {struct l} :
   list B := match l with
             | nil => nil
             | a :: l => f a :: F _ _ f l
             end).

(* V8 printing of this term used to failed in V8.0 and V8.0pl1 (cf BZ#860) *)
Check
  let fix f (m : nat) : nat :=
    match m with
    | O => 0
    | S m' => f m'
    end
  in f 0.

Inductive even : nat -> Type :=
  | even_O : even 0
  | even_S : forall n, odd n -> even (S n)
with odd : nat -> Type :=
    odd_S : forall n, even n -> odd (S n).

(* Check printing of fix *)
Ltac f id1 id2 := fix id1 2 with (id2 n (H:odd n) {struct H} : n >= 1).
Print Ltac f.

CoInductive Inf := IS { projS : Inf }.
Definition expand_Inf (x : Inf) := IS (projS x).
CoFixpoint inf := IS inf.
Eval compute in inf.

Module Recursivity.

Open Scope nat_scope.

Fixpoint f n := match n with 0 => 0 | S n => f n end.
Fixpoint g n := match n with 0 => 0 | S n => n end.
Fixpoint h1 n := match n with 0 => 0 | S n => h2 n end
with h2 n := match n with 0 => 0 | S n => h1 n end.
Fixpoint k1 n := match n with 0 => 0 | S n => k2 n end
with k2 n := match n with 0 => 0 | S n => n end.
Fixpoint l1 n := match n with 0 => 0 | S n => l1 n end
with l2 n := match n with 0 => 0 | S n => l2 n end.
Fixpoint m1 n := match n with 0 => 0 | S n => m1 n end
with m2 n := match n with 0 => 0 | S n => n end.
(* Why not to allow this definition ?
Fixpoint h1' n := match n with 0 => 0 | S n => h2' n end
with h2' n := h1' n.
*)
CoInductive S := cons : nat -> S -> S.
CoFixpoint c := cons 0 c.
CoFixpoint d := cons 0 c.
CoFixpoint e1 := cons 0 e2
with e2 := cons 1 e1.
CoFixpoint a1 := cons 0 a1
with a2 := cons 1 a2.
(* Why not to allow this definition ?
CoFixpoint b1 := cons 0 b2
with b2 := b1.
*)

End Recursivity.

Module Guard.

Open Scope nat_scope.

Lemma foo : nat -> nat -> bool
with bar : nat -> nat -> bool.
Proof.
  Fail Guarded. (* not enough abstractions in the definition *)
  all:intros n m.
  Guarded.
  - destruct n as [|n].
    + exact (bar 0 0).
      Fail Guarded. (* failure is correct here *)
Abort.

Lemma foo : nat -> nat -> bool
with bar : nat -> nat -> bool.
Proof.
  all:intros n m.
  - destruct n as [|n].
    + exact true.
    + Guarded.
      exact (bar m n).
  - Guarded.
    destruct m as [|m].
    + exact false.
    + exact (foo m n).
      Guarded.
Defined.

Inductive STrue : SProp := SI.

Lemma foo' : nat -> Prop -> bool
with bar' : STrue -> nat -> bool.
Proof.
  all:intros n m.
  - destruct n as [|n].
    Guarded.
    + exact (bar' SI 0).
      Fail Guarded.
Abort.

End Guard.
