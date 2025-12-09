Set Universe Polymorphism.

Definition T@{u} : Set := unit.
Definition U@{u} : Type@{u+1} := Type@{u}.

Definition anomaly := (tt <: T).
Definition anomaly' := (Type <: U).

Definition native_anomaly := (tt <<: T).
Definition native_anomaly' := (Type <<: U).
