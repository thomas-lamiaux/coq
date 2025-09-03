From Ltac2 Require Import Ltac2.
Lemma foo n m : S n = S m -> n = m.
Proof.
  intros [= x].
  exact x.
Qed.
