Class UnivSubst := subst : unit.

Module Type Term.
  Parameter subst1 : UnivSubst.
End Term.

Module Environment (T : Term).

#[global] Existing Instance T.subst1.

End Environment.

Module PCUICTerm.
  (* if we do ": UnivSubst" here we get the same error in master as in PR#21193 *)
  Definition subst1 : unit := tt.
End PCUICTerm.

Module Export PCUICEnvironment := Environment PCUICTerm.

Definition infer := subst.
