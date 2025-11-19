Class A := a : True.
Hint Extern 1 A => abstract exact I : typeclass_instances.
Check _ : A. (* failure with error in 8.4, anomaly in 8.5rc1 *)
