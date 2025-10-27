(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
Set Debug "backtrace".
Set Printing Universes.
Set Printing Relevance Marks.

Notation "A -> B" := (forall (_ : A), B) (right associativity, at level 99).

Inductive unit := tt.

Inductive True : Prop :=
  I : True.

(** [False] is the always false proposition *)
Inductive False : Prop :=.

Inductive nat : Type :=
| zero : nat
| suc : nat -> nat.

Inductive bool : Type :=
| true : bool
| false : bool.

(* Bnat *)
Inductive bnat : Type :=
| bO : bnat
| bS : bnat -> bnat -> bool -> bnat.

(* Infinitely branching tree *)
Inductive ftree : Type :=
| fleaf : ftree
| fnode : (nat -> ftree) -> ftree.

Inductive ftree2 : Type :=
| fleaf2 : ftree2
| fnode2 : (nat -> bool -> ftree2) -> ftree2.

Inductive nat2 : Type :=
| zero2 : nat2
| suc2 : nat2 -> nat2 -> nat2 -> nat2.

(* uparams *)

Inductive list (A : Type) : Type :=
 | nil : list A
 | cons : A -> list A -> list A.

Inductive prod (A B:Type) : Type :=
  pair : A -> B -> prod A B.

Inductive and (A B : Prop) : Prop :=
  conj : A -> B -> and A B.

Inductive or (A B : Prop) : Prop :=
  | or_introl : A -> or A B
  | or_intror : B -> or A B.

Inductive orbis (A B:Prop) : Prop :=
  | orbis_introl : A -> orbis A B
  | orbis_intror : A -> B -> orbis A B.

Inductive prod4 (A B C D : Type) : Type :=
| pair4 : A -> B -> C -> D -> prod4 A B C D.

Inductive ftreep (A : Type) : Type :=
| fleafp : A -> ftreep A
| fnodep : (nat -> ftreep A) -> ftreep A.

Inductive ftreep2 (A : Type) : Type :=
| fleafp2 : A -> ftreep2 A
| fnodep2 : (nat -> bool -> ftreep2 A) -> ftreep2 A.

Inductive tricky A : Type :=
| tricky1 : (bool -> A) -> tricky A.

(* indices *)
Inductive vec1 : nat -> Type :=
| vnil1    : vec1 zero
| vcons1 n : vec1 n -> vec1 (suc n).

Inductive vec2 : nat -> bool -> Type :=
| vnil2     : vec2 zero true
| vcons2  n : vec2 n false -> vec2 (suc n) true.

Inductive vec3 (A : Type) : nat -> Type :=
| vnil3    : vec3 A zero
| vcons3 n : A -> vec3 A n -> vec3 A (suc n).

Inductive vec4 (A B : Type) : nat -> bool -> Type :=
| vnil4 (a : A)    : vec4 A B zero true
| vcons4 (b : B) n : vec4 A B n false.

Inductive vec5 (A B : Type) : nat -> nat -> Type :=
| vnil5  (a : A)    : vec5 A B zero zero
| vcons5 (b : B) n m : vec5 A B n m.

Inductive myeq (A : Type) (x:A) : A -> Prop :=
    myeq_refl : myeq A x x.


Inductive foo (A : Type) : list A -> Type :=
| cf : foo A (@nil A).

Inductive vectree A : nat -> Type :=
| vleaf : A -> vectree A zero
| vnode : forall n, (nat -> vectree A n) -> vectree A (suc n).

Inductive vectree2 A : nat -> Type :=
| vleaf2 : A -> vectree2 A zero
| vnode2 : forall n, (nat -> bool -> vectree2 A n) -> vectree2 A (suc n).




(* mutual *)

Inductive teven : Prop :=
| teven0 : teven
| tevenS : todd -> teven
with
todd : Prop :=
| toddS : teven -> todd.

Inductive even : nat -> Type :=
| even0   : even zero
| evenS n : odd n -> even (suc n)
with
odd : nat -> Type :=
| oddS n : even n -> odd (suc n).


(* non uniform *)

(* nb_uparams: zero *)
Inductive nu_list (A : Type) : Type :=
| nu_nil : nu_list A
| nu_cons : nu_list (prod A A) -> nu_list A.

(* nb_uparams: 1 *)
Inductive mixed1 (A B C : Type) : Type :=
| mc11 : mixed1 A B C
| mc12 : mixed1 A nat C -> mixed1 A B C.

(* nb_uparams: zero *)
Inductive mixed2 (A B C : Type) : Type :=
| mc21 : mixed2 A bool C -> mixed2 A B C
| mc22 : mixed2 nat B C -> mixed2 A B C.

(* nb_uparams: zero *)
Inductive mixed3 (A B C D : Type) : Type :=
| mc31 : mixed3 A B C bool -> nat -> mixed3 A B C D
| mc32 : mixed3 A B nat D -> nat -> mixed3 A B C D
| mc33 : nat -> mixed3 A B bool D -> mixed3 A B C D
| mc34 : mixed3 nat B C D -> mixed3 A B C D -> mixed3 A B C D
| mc35 : mixed3 A nat C D -> mixed3 B A C D -> mixed3 A B C D.

(* nb_uparams: zero *)
Inductive nu_vec (n : nat) : Type :=
| vnil_pa : nu_vec n
| vcons_pa : nu_vec (suc n) -> nu_vec n.

(* nb_uparams: zero *)
Inductive nu_ftree A : Type :=
| nufleaf : A -> nu_ftree A
| nufnode : (nat -> nu_ftree (prod A A)) -> nu_ftree A.

(* nb_uparams: zero *)
Inductive nu_ftree2 A : Type :=
| nufleaf2 : A -> nu_ftree2 A
| nufnode2 : (nat -> bool -> nu_ftree2 (prod A A)) -> nu_ftree2 A.


(* nb_uparams : 3 *)
(* strpos : [false, false, true] *)
Inductive sAll2i (R : nat -> bool -> bool -> Type) (n : nat) : Type :=
	| sAll2i_nil : sAll2i R n
  | sAll2i_cons : forall (a : bool) (b : bool),
                 R n a b -> sAll2i R (suc n) -> sAll2i R n.

Inductive All2i (A B : Type) (R : nat -> A -> B -> Type) (n : nat) : list A -> list B -> Type :=
	| All2i_nil : All2i A B R n ( nil A) (nil B)
  | All2i_cons : forall (a : A) (b : B) (lA : list A) (lB : list B),
                 R n a b -> All2i A B R (suc n) lA lB -> All2i A B R n (cons A a lA) (cons B b lB).

Inductive RoseTree : Type :=
| node : list RoseTree -> RoseTree.

Inductive slist (A B : Type) (C : Type) : Type :=
| snil  : slist A B C
| scons (a : A) (b : B) (c : C) : slist A B C -> slist A B C.





Inductive rc_let (A : Type) : Type :=
| rc_letz : rc_let A
| rc_lets (a : A) : let x := rc_let A in x -> rc_let A.

Inductive rc_letpar (A : Prop) : Type :=
| rc_letparz : rc_letpar A
| rc_letpars (n m : nat) : rc_letpar A -> (let y := rc_letpar A in y) -> rc_letpar A.

Inductive crazy1 : nat -> Type :=
| crazy1_z : crazy1 zero
| crazy1_s (n : nat) : let x := suc n in crazy1 x.

Inductive diag : nat -> nat -> Type :=
| dcons c : diag c c -> let ptm := c in diag c c.

Inductive redc : nat -> Type :=
| redc0 : redc zero
| redc1 n : (redc ((fun x => suc (suc x)) n)) -> redc n.

Definition id : Type -> Type := fun x => x.

Inductive redEnv : Type :=
| redEnv0 : redEnv
| redEnv1 : redEnv -> id redEnv -> redEnv.

Inductive nu_let1 (A : Type) : Type :=
| nu_let1_nil : nu_let1 A
| nu_let1_cons : let x := A in nu_let1 x -> nu_let1 A.

Inductive nu_let2 (A : Type) : Type :=
| nu_let2_nil : nu_let2 A
| nu_let2_cons : let x := prod A A in nu_let2 x -> nu_let2 A.





(* Test des definitions inductives imbriquees *)

Inductive X : Set :=
  cons1 : list X -> X.

Inductive Y : Set :=
  cons2 : list (prod Y Y) -> Y.

(* Test inductive types with local definitions (arity) *)

Inductive eq1 : forall A:Type, let B:=A in A -> Prop :=
  refl1 : eq1 True I.

Inductive eq2 (A:Type) (a : A) : forall B C : Type, let D:= (prod A (prod B C)) in D -> Prop :=
  refl2 : eq2 A a unit bool (pair _ _ a (pair _ _ tt true)).

(* Check inductive types with local definitions (parameters) *)

Inductive LetInIndices (A B : Prop) (E:=A) (F:=B) (f g : E -> F) : E -> Set :=
    CIn : forall e : E, LetInIndices A B f g e.

Inductive I1 : Set := C1 (_:I1) (_:=zero).

Set Implicit Arguments.
Unset Strict Implicit.

CoInductive LList (A : Set) : Set :=
  | LNil : LList A
  | LCons : A -> LList A -> LList A.

Arguments LNil {A}.

Inductive Finite (A : Set) : LList A -> Prop :=
  | Finite_LNil : Finite LNil
  | Finite_LCons :
      forall (a : A) (l : LList A), Finite l -> Finite (LCons a l).

(* Check inference of evars in arity using information from constructors *)

Inductive foo1 : forall p, Prop := cc1 : foo1 zero.

Inductive foo2 : forall p, Prop := cc2 : forall q, foo2 q | cc3 : foo2 zero.

Inductive IND1 (A:Type) := CONS1 : IND1 ((fun x => A) IND1).

Inductive IND2 (A:Type) (T:=fun _ : Type->Type => A) : Type :=
| CONS2 : IND2 A -> IND2 (T IND2).

Inductive IND3 (A:Type) (T:=fun _ : Type->Type => A) : Type :=
| CONS3 : IND3 (T IND3) -> IND3 A.

Inductive IND4 (A:Type) : Type :=
| CONS4 : IND4 ((fun x => A) IND4) -> IND4 A.

Inductive IND5 (A : Type) (T := A) : Type :=
| CONS5 : IND5 ((fun _ => A) zero) -> IND5 A.

Inductive IND6 (B : Type) (A := nat) : A -> Type :=
| CONS6 n : IND6 (prod B B) n -> IND6 B n.

Inductive list' (A:Type) (B:=A) :=
| nil' : list' A
| cons' : A -> list' B -> list' A.

Inductive tree := node' : list' tree -> tree.

Inductive L (A : Type) (T := A) B : Type :=
  CONSL : B -> L A B -> L T B.

Inductive IND7 (A:Type) (T:=A) := CONS7 : IND7 T -> IND7 A.

Inductive IND8 : nat -> Type :=
| CONS8 (n := zero) : IND8 n -> let m := zero in IND8 m.

(* Module TemplateProp.

  (** Check lowering of a template universe polymorphic inductive to Prop *)

  Inductive Foo (A : Type) : Type := foo : A -> Foo A.

  Check Foo True : Prop.

End TemplateProp. *)

(* Module PolyNoLowerProp.

  (** Check lowering of a general universe polymorphic inductive to Prop is _failing_ *)

  Polymorphic Inductive Foo (A : Type) : Type := foo : A -> Foo A.

  Fail Check Foo True : Prop.

End PolyNoLowerProp. *)

(* Test building of elimination scheme with noth let-ins and
   non-recursively uniform parameters *)

Module NonRecLetIn.

  Unset Implicit Arguments.

  Inductive Ind (b:=suc (suc zero)) (a:nat) (c:=suc zero) : Type :=
  | Base : Ind a
  | Rec : Ind (suc a) -> Ind a.

End NonRecLetIn.

Section Well_founded.

 Variable A : Type.
 Variable R : A -> A -> Prop.

 (** The accessibility predicate is defined to be non-informative *)
 (** (Acc_rect is automatically defined because Acc is a singleton type) *)

 Inductive Acc (x: A) : Prop :=
     Acc_intro : (forall y : A, R y x -> Acc y) -> Acc x.

End Well_founded.

Inductive letfoo (n := zero) A :=
| letFoo : letfoo nat -> letfoo A.

Polymorphic Inductive polyuin (A : Type): Type := C.

Inductive pFalse : Prop  := .

Inductive sFalse : SProp := .

(*

Module M0.

Inductive foo (A : Type) := Foo {
  foo1 : nat;
  foo2 := myeq _ foo1 zero;
  foo3 : foo2;
}

with bar (A : Type) := Bar {
  bar0 : A;
  bar1 := zero;
  bar2 : myeq _ bar1 zero;
  bar3 : nat -> foo A;
}.

End M0.

Module M1.

Set Primitive Projections.

Inductive foo (A : Type) := Foo {
  foo1 : nat;
  foo2 := myeq _ foo1 zero;
  foo3 : foo2;
}

with bar (A : Type) := Bar {
  bar0 : A;
  bar1 := zero;
  bar2 : myeq _ bar1 zero;
  bar3 : nat -> foo A;
}.

End M1.

Module M2.

Set Primitive Projections.

CoInductive foo (A : Type) := Foo {
  foo1 : nat;
  foo2 := myeq _ foo1 zero;
  foo3 : foo2;
}

with bar (A : Type) := Bar {
  bar0 : A;
  bar1 := zero;
  bar2 : myeq _ bar1 zero;
  bar3 : nat -> foo A;
}.

End M2. *)