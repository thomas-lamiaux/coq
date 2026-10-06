Require Import Program.Wf.

Unset Guard Checking Option Traversing Subterm Analysis.

Lemma nat_wf : well_founded lt.
Proof.
  intros a; constructor.
  induction a.
  all: intros y H; inversion H; eauto.
  now constructor.
Defined.

(* Check the selected constant, rather than relying only on computation. *)
Ltac uses_original f :=
  let body := eval unfold f in f in
  lazymatch body with
  | context [@Fix_sub] => idtac
  | _ => fail "expected Fix_sub"
  end.

Ltac uses_structural f :=
  let body := eval unfold f in f in
  lazymatch body with
  | context [@Fix_sub_struct] => idtac
  | _ => fail "expected Fix_sub_struct"
  end.

Module Original.

  Set Guard Checking Option Traversing Subterm Analysis.
  Program Fixpoint f x {wf lt x} :=
    match x with 0 => 0 | S n => S (f n) end.

  (* The choice is fixed before the well-foundedness obligation is solved. *)
  Unset Guard Checking Option Traversing Subterm Analysis.
  Final Obligation.
    unfold MR; exact nat_wf.
  Defined.

  Goal True.
  Proof.
    uses_original f.
    exact I.
  Qed.

  Definition fid n : f n = n.
  Proof.
    induction n; try reflexivity.
    transitivity (S (f n)). 2: now f_equal.
    cbv; reflexivity.
  Fail Qed.
  Abort.

End Original.

Module Structural.

  Unset Guard Checking Option Traversing Subterm Analysis.
  Program Fixpoint f x {wf lt x} :=
    match x with 0 => 0 | S n => S (f n) end.

  Set Guard Checking Option Traversing Subterm Analysis.
  Final Obligation.
    intros ?. constructor. unfold MR.
    induction a.
    all: unfold MR; cbn; intros.
    all: inversion H; eauto.
    now constructor.
  Defined.
  Unset Guard Checking Option Traversing Subterm Analysis.

  Goal True.
  Proof.
    uses_structural f.
    exact I.
  Qed.

  Definition fid n : f n = n.
  Proof.
    induction n; try reflexivity.
    transitivity (S (f n)). 2: now f_equal.
    cbv; reflexivity.
  Qed.

  (* A measure over multiple arguments, with an opaque obligation. *)
  #[program]
  Fixpoint add (n m : nat) {measure n} : nat :=
    match n with 0 => m | S p => S (add p m) end.
  Final Obligation.
    apply measure_wf; exact nat_wf.
  Qed.

  Goal True.
  Proof.
    uses_structural add_func.
    exact I.
  Qed.

  Goal forall m, add 0 m = m.
  Proof.
    intro m.
    Fail reflexivity.
    unfold add, add_func.
    rewrite fix_sub_struct_eq.
    - reflexivity.
    - intros [n m'] g h Heq; cbn.
      destruct n; [reflexivity | f_equal; apply Heq].
  Qed.

  Goal forall n, f n = f n.
  Proof.
    intro n; unfold f at 1.
    fold_sub f.
    reflexivity.
  Qed.

  (* The return type depends on the argument used by the measure. *)
  Program Fixpoint bounded (n : nat) {measure n} : {m : nat | m <= n} :=
    match n with 0 => 0 | S p => bounded p end.
  Next Obligation.
    destruct (bounded p); cbn in *; auto.
  Qed.
  Final Obligation.
    apply measure_wf; exact nat_wf.
  Qed.

  Goal True.
  Proof.
    uses_structural bounded.
    exact I.
  Qed.

  (* The new induction principle does not unfold opaque accessibility proofs. *)
  Goal forall n, f n = n.
  Proof.
    unfold f.
    apply Fix_sub_struct_rect with (Q := fun n v => v = n).
    - intros x g h Heq; cbn.
      destruct x; [reflexivity | f_equal; apply Heq].
    - intros x IH a; cbn.
      destruct x; [reflexivity | f_equal; apply IH; constructor].
  Qed.

End Structural.
