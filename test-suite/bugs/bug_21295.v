Axioms (A:Type) (B:Type) (a:A).

Module Type DecidableType.
  Parameter Inline(30) coe : A -> B.
End DecidableType.

Axiom default_coe : A -> B.

Module Type UsualOrderedType.
  Definition coe := default_coe.
End UsualOrderedType.

Module WDecideOn (E : DecidableType).
  Coercion E.coe : A >-> B.
End WDecideOn.

Module WeightedGraph (V : UsualOrderedType).
  Module E := V.

  Module Import VSetDecide := WDecideOn E.

  Lemma VSet_add_remove : B.
  Proof.
    exact a.
  Defined.
End WeightedGraph.
