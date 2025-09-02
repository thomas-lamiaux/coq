Module Type Typ.
End Typ.

Module Inst.

Module E. End E.

End Inst.

Module F (Z : Typ).
  Module IN (X : Typ).
  End IN.
End F.

Module Fun (Y : Typ).
  Module ARG := F Y.
End Fun.

Module Map (M2 : Typ).
  Module OUT := Fun M2.
End Map.

Module Bug : Typ := Map Inst.
