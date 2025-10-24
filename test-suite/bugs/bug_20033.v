Set Implicit Arguments.

Record Monad : Type := {
  functor  :> Type -> Type ;
  ret      : forall  T   : Type, T -> functor T ;
  bind     : forall  T U : Type, functor T -> (T -> functor U) -> functor U ;
  left_id  : forall (T U : Type) (t : T) (f : T -> functor U), bind (ret t) f = f t ;
}.

Program Definition IdMonad : Monad := {|
  functor := fun X => X ;
  ret := fun _ t => t ;
  bind := fun _ _ t f => f t
|}.

Lemma ft_equal : forall (T U : Type) (t : T) (f : T -> U), f t = f t.
Proof.
    reflexivity.
Qed.

Final Obligation.
  apply ft_equal.
Qed.
