Module A.
  Lemma andb_false_r b : andb b false = false.
  Proof. case b; reflexivity. Qed.

  #[export] Hint Rewrite andb_false_r : bool_rew.
End A.


Import (hints) A.

Goal forall b, andb b false = false.
Proof.
  intro.
  autorewrite with bool_rew.
  reflexivity.
Qed.
