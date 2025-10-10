Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Record pType@{u} : Type@{u+1} := { pointed_type : Type@{u} }.

Class IsGraph@{u} (A : Type@{u}) : Set := { }.

Record CatEquiv@{u} {A : Type@{u}} {G : IsGraph@{u} A} (a b : A) : Set := {}.

Declare Instance isgraph_ptype@{u v|u < v} : IsGraph@{v} pType@{u}.

Axiom pfiber@{u} : pType@{u}.

Set Typeclasses Debug.

Axiom pequiv_pfiber : CatEquiv pfiber pfiber.
(* succeeds on master, on this PR fails with
Illegal application:
The term "@CatEquiv@{Top.29}" of type "forall A : Type@{Top.29}, IsGraph@{Top.29} A -> A -> A -> Set"
cannot be applied to the terms
 "pType@{Top.30}" : "Type@{Top.30+1}"
 "isgraph_ptype@{Top.32 Top.29}" : "IsGraph@{Top.29} pType@{Top.32}"
 "pfiber@{Top.30}" : "pType@{Top.30}"
 "pfiber@{Top.31}" : "pType@{Top.31}"
The 2nd term has type "IsGraph@{Top.29} pType@{Top.32}" which should be a subtype of
 "IsGraph@{Top.29} pType@{Top.30}". *)
