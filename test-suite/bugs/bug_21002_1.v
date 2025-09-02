Module Type Typ.
  Parameter Inline(10) t : Type.
End Typ.

Module Make_UDTF (M: Typ) := M.

Axiom R : Set.

Module Foo.

Module R_as_UBE.
 Definition t := R.
End R_as_UBE.

Module R_as_DT := Make_UDTF R_as_UBE.

Module R_as_OT.
  Include R_as_DT.
End R_as_OT.

End Foo.
