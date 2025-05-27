Require Import Ltac2.Ltac2.

Definition foo : nat := 1.
Opaque foo.

Goal True /\ False.
  (* conversion works *)
  Control.assert_true (Unification.conv_full '4 '(2 + 2)).
  (* conversion fails *)
  Fail Control.assert_true (Unification.conv_full '4 '3).
  (* at most one goal must be focussed *)
  split. Fail all: Unification.conv_full '4 '(2 + 2).
  (* constants are respected *)
  Fail Control.assert_true (Unification.conv_current 'foo '1).
  Control.assert_true (Unification.conv_full 'foo '1).
  (* its the local env that is used *)
  pose (x := 1); Control.assert_true (Unification.conv_full '&x '1).
Abort.
