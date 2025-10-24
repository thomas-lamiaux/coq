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

Notation "A -> B" := (forall (_ : A), B) (right associativity, at level 99).

Inductive True : Prop :=
  I : True.

(** [False] is the always false proposition *)
Inductive False : Prop :=.

Inductive and (A B : Prop) : Prop :=
  conj : A -> B -> and A B.

Inductive or (A B:Prop) : Prop :=
  | or_introl : A -> or A B
  | or_intror : B -> or A B.

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

Inductive even : nat -> Prop :=
| even0   : even zero
| evenS n : odd n -> even (suc n)
with
odd : nat -> Prop :=
| oddS n : even n -> odd (suc n).


(* non uniform *)

(* nb_uparams: 0 *)
Inductive nu_list (A : Type) : Type :=
| nu_nil : nu_list A
| nu_cons : nu_list (prod A A) -> nu_list A.

(* nb_uparams: 1 *)
Inductive mixed1 (A B C : Type) : Type :=
| mc11 : mixed1 A B C
| mc12 : mixed1 A nat C -> mixed1 A B C.

(* nb_uparams: 0 *)
Inductive mixed2 (A B C : Type) : Type :=
| mc21 : mixed2 A bool C -> mixed2 A B C
| mc22 : mixed2 nat B C -> mixed2 A B C.

(* nb_uparams: 0 *)
Inductive mixed3 (A B C D : Type) : Type :=
| mc31 : mixed3 A B C bool -> nat -> mixed3 A B C D
| mc32 : mixed3 A B nat D -> nat -> mixed3 A B C D
| mc33 : nat -> mixed3 A B bool D -> mixed3 A B C D
| mc34 : mixed3 nat B C D -> mixed3 A B C D -> mixed3 A B C D
| mc35 : mixed3 A nat C D -> mixed3 B A C D -> mixed3 A B C D.

(* nb_uparams: 0 *)
Inductive nu_vec (n : nat) : Type :=
| vnil_pa : nu_vec n
| vcons_pa : nu_vec (suc n) -> nu_vec n.

(* nb_uparams: 0 *)
Inductive nu_ftree A : Type :=
| nufleaf : A -> nu_ftree A
| nufnode : (nat -> nu_ftree (prod A A)) -> nu_ftree A.

(* nb_uparams: 0 *)
Inductive nu_ftree2 A : Type :=
| nufleaf2 : A -> nu_ftree2 A
| nufnode2 : (nat -> bool -> nu_ftree2 (prod A A)) -> nu_ftree2 A.


(* nb_uparams : 3 *)
(* strpos : [false, false, true] *)
Inductive All2i (A B : Type) (R : nat -> A -> B -> Type) (n : nat) : list A -> list B -> Type :=
	| All2i_nil : All2i A B R n ( nil A) (nil B)
  | All2i_cons : forall (a : A) (b : B) (lA : list A) (lB : list B),
                 R n a b -> All2i A B R (suc n) lA lB -> All2i A B R n (cons A a lA) (cons B b lB).

Inductive RoseTree : Type :=
| node : list RoseTree -> RoseTree.

Inductive slist (A B : Type) (C : Type) : Type :=
| snil  : slist A B C
| scons (a : A) (b : B) (c : C) : slist A B C -> slist A B C.



(* Inductive b_let (A : Type) : Type :=
| b_letz : b_let A
| b_lets (n m : nat) : let x := n + 0 in x = m -> x = m + 1 -> b_let A -> b_let A. *)

Inductive rc_let (A : Type) : Type :=
| rc_letz : rc_let A
| rc_lets (a : A) : let x := rc_let A in x -> rc_let A.

Inductive rc_letpar (A : Prop) : Type :=
| rc_letparz : rc_letpar A
| rc_letpars (n m : nat) : rc_letpar A -> (let y := rc_letpar A in y) -> rc_letpar A.

Inductive crazy1 : nat -> Type :=
| crazy1_z : crazy1 zero
| crazy1_s (n : nat) : let x := suc n in crazy1 x.

(* Inductive crazy2 (A : let y := Prop in or y Prop) : (let y := bool in or bool nat) -> Type :=
| crazy2_z : crazy2 A (inr 0)
| crazy2_s (k n m : nat) : let x := n + 0 in x = m -> x = m + 1 -> crazy2 A (inl true) ->
                     let z := 0 in crazy2 A (let y := 0 in inr (x + y)). *)

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