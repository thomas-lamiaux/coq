Require Import Program.Basics Program.Tactics.

Obligation Tactic := abstract exact I.

Program Definition foo : True := _.

Definition bar : True := ltac:(abstract exact I).
