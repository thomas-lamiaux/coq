Module Base.
Inductive Zmod := of_N.
End Base.

Module bar.

Module biz.
  Include Base.
End biz.

End bar.

Include bar.
(* in coqchk: Inductive Tmp.foo.biz.Zmod does not appear in the environment. *)
