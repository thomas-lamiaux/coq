Inductive JMeq [A] (x : A) : forall [B], B -> Prop :=  JMeq_refl : JMeq x x.

Scheme Rewriting for JMeq.
