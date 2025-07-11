Require Corelib.extraction.Extraction.

Module Type S.
  Parameter t : Type.
  Parameter fold : t.
End S.

Module M : S.
  Definition t := list unit -> unit.
  Fixpoint fold (l : list unit) : unit :=
    match l with
    | nil => tt
    | cons b l =>
      match b with
      | tt => fold l
      end
    end.
End M.

Axiom bug : M.t.

Extraction bug.
