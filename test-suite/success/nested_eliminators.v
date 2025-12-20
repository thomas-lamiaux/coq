Notation "A -> B" := (forall (_ : A), B) (right associativity, at level 99).

Set Printing Universes.

Inductive nat : Type :=
| zero : nat
| S : nat -> nat.

Inductive bool : Type :=
| true : bool
| false : bool.

(* The type True needs to be defined and registered to instantiate constant nesting. *)
Inductive True : Prop :=
  I : True.

Register True as core.True.type.
Register I as core.True.I.


Module Template.

  (* Example with Template Inductive Types *)

  (* Example with list *)
  Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.

  Arguments nil {_}.
  Arguments cons {_}.

  Infix "::" := cons (at level 60, right associativity) : list_scope.

  Scheme SparseParametricity for list.
  Scheme SparseParametricity for list_all.
  Scheme SparseParametricity for list_all_all.
  Scheme SparseParametricity for list_all_all_all.

  #[universes(polymorphic)]
  Definition lfth_list_all@{sP; uP+} A (PA : A -> Type@{sP;uP}) (HPA : forall pA : A, PA pA) :=
    fix F0_list (x : list A) : list_all A PA x :=
    match x as H return (list_all A PA H) with
    | nil => nil_all A PA
    | cons x0 x1 => cons_all A PA x0 (HPA x0) x1 (F0_list x1)
    end.

  (* register the local fundamental theorem *)
  Register Scheme lfth_list_all as local_fundamental_theorem for list.

  Inductive MRT : Set :=
  | MRTnode : list MRT -> MRT.

  (* Scheme SparseParametricity for MRT. *)

  Inductive RoseTree A : Type :=
  | RTleaf (a : A) : RoseTree A
  | RTnode (l : list (RoseTree A)) : RoseTree A.

  Scheme SparseParametricity for RoseTree.

  Inductive RoseRoseTree A : Type :=
  | Nleaf (a : A) : RoseRoseTree A
  | Nnode (p : (list (list (RoseRoseTree A)))) : RoseRoseTree A.

  Scheme SparseParametricity for RoseRoseTree.

  Inductive ArrowTree1 A : Type :=
  | ATleaf1 (a : A) : ArrowTree1 A
  | ATnode1 (l : (bool -> list (ArrowTree1 A))) : ArrowTree1 A.

  Scheme SparseParametricity for ArrowTree1.

  Inductive ArrowTree2 A : Type :=
  | ATleaf2 (a : A) : ArrowTree2 A
  | ATnode2 (l : list (nat -> ArrowTree2 A)) : ArrowTree2 A.

  Scheme SparseParametricity for ArrowTree2.

  Inductive ArrowTree3 A : Type :=
  | ATleaf3 (a : A) : ArrowTree3 A
  | ATnode3 (l : (bool -> list (nat -> ArrowTree3 A))) : ArrowTree3 A.

  Scheme SparseParametricity for ArrowTree3.

  (* Example Prod *)
  Inductive prod (A B : Type) : Type :=
    pair : A -> B -> prod A B.

  Arguments pair {_ _}.

  Scheme SparseParametricity for prod.

  #[universes(polymorphic)]
  Definition lfth_prod_all@{sa sb ; ua ub +} A (PA : A -> Type@{sa;ua}) (HPA : forall a, PA a)
                        B (PB : B -> Type@{sb|ub}) (HPB : forall b, PB b) :
                        forall (x : prod A B), prod_all A PA B PB x :=
    fun x => match x with
    | pair a b => pair_all A PA B PB a (HPA a) b (HPB b)
    end.

  Register Scheme lfth_prod_all as local_fundamental_theorem for prod.

  Inductive PairTree A : Type :=
  | Pleaf (a : A) : PairTree A
  | Pnode (p : prod (PairTree A) (PairTree A)) : PairTree A.

  Scheme SparseParametricity for PairTree.

  Inductive LeftTree A : Type :=
  | Lleaf (a : A) : LeftTree A
  | Lnode (p : prod (LeftTree A) nat) : LeftTree A.

  (* Scheme SparseParametricity for LeftTree. *)

  Inductive RightTree A : Type :=
  | Rleaf (a : A) : RightTree A
  | Rnode (p : prod nat (RightTree A)) : RightTree A.

  (* Scheme SparseParametricity for RightTree. *)

  Inductive nu_nested (A B C : Type) : Type :=
  | nu_nested_nil : A -> nu_nested A B C
  | nu_nested_cons : list (nu_nested A (prod B B) C) -> nu_nested A B C.

  Scheme SparseParametricity for nu_nested.

  Inductive tricky1 A : Type :=
  | tricky11 : prod A nat -> tricky1 A.

  (* Scheme SparseParametricity for tricky1. *)

  Inductive tricky2 A : Type :=
  | tricky21 : list A -> tricky2 A.

  Scheme SparseParametricity for tricky2.

  Inductive tricky3 A : Type :=
  | tricky31 : prod A A -> tricky3 A
  | tricky32 : prod (list A) A -> tricky3 A.

  Scheme SparseParametricity for tricky3.


  (* Nesting with vec *)
  Inductive vec A : nat -> Type :=
  | vnil : vec A zero
  | vcons : A -> forall n, vec A n -> vec A (S n).

  Scheme SparseParametricity for vec.

  #[universes(polymorphic)]
  Fixpoint lfth_vec_all@{s;ua+} A (PA : A -> Type@{s;ua}) (HPA : forall a : A, PA a)
              n v : vec_all A PA n v :=
    match v with
    | vnil _ => vnil_all A PA
    | vcons _ a n v => vcons_all A PA a (HPA a) n v (lfth_vec_all A PA HPA n v)
    end.

  Register Scheme lfth_vec_all as local_fundamental_theorem for vec.

  Inductive VecTree A : Type :=
  | VNleaf (a : A) : VecTree A
  | VNnode n (p : vec (VecTree A) n) : VecTree A.

  Scheme SparseParametricity for VecTree.


  (* Example All2i *)
  Inductive All2i (A B : Type) (R : nat -> A -> B -> Type) (n : nat) : list A -> list B -> Type :=
    | All2i_nil : All2i A B R n nil nil
    | All2i_cons : forall (a : A) (b : B) (lA : list A) (lB : list B),
                  R n a b -> All2i A B R (S n) lA lB -> All2i A B R n (cons a lA) (cons b lB).

  Arguments All2i_nil {_ _ _ _ }.
  Arguments All2i_cons {_ _ _ _}.

  Scheme SparseParametricity for All2i.

  Arguments All2i_nil_all {_ _ _ _ _}.
  Arguments All2i_cons_all {_ _ _ _ _}.

  #[universes(polymorphic)]
  Definition lfth_All2i_all@{sr;ur+} (A B : Type) (R : nat -> A -> B -> Type)
    (PR : forall n a b, R n a b -> Type@{sr;ur}) (HPR : forall n a b r, PR n a b r) :
    forall n la lb x, All2i_all A B R PR n la lb x :=
    fix f n la lb x : All2i_all A B R PR n la lb x :=
    match x with
    | All2i_nil => All2i_nil_all
    | All2i_cons a b lA lB r x => All2i_cons_all a b lA lB r (HPR n a b r) x (f (S n) lA lB x)
    end.

  Register Scheme lfth_All2i_all as local_fundamental_theorem for All2i.

  Inductive typing A B (n : nat) (a : A) (b : B) : Type :=
  | typ_nil  : typing A B n a b
  | typ_cons : forall (lA : list A) (lB : list B),
              All2i A B (fun n => typing A B n) n lA lB -> typing A B n a b.

  Scheme SparseParametricity for typing.

  (* Example All2i_bis_bis with trivial nesting on R *)
  Inductive All2i_bis (A B C : Type) (R : nat -> A -> B -> Type) (n : nat) : list A -> list B -> Type :=
    | All2i_bis_nil : C -> All2i_bis A B C R n nil nil
    | All2i_bis_cons : forall (a : A) (b : B) (lA : list A) (lB : list B),
                  R n a b -> All2i_bis A B C R (S n) lA lB -> All2i_bis A B C R n (cons a lA) (cons b lB).

  Arguments All2i_bis_nil  {_ _ _ _ _}.
  Arguments All2i_bis_cons {_ _ _ _ _}.

  Scheme SparseParametricity for All2i_bis.

  Arguments All2i_bis_nil_all  {_ _ _ _ _ _ _}.
  Arguments All2i_bis_cons_all {_ _ _ _ _ _ _}.

  #[universes(polymorphic)]
  Definition lfth_All2i_bis_all@{sc sr ; uc ur+} (A B C : Type) (PC : C -> Type@{sc;uc}) (HPC : forall c, PC c) (R : nat -> A -> B -> Type)
    (PR : forall n a b, R n a b -> Type@{sr;ur}) (HPR : forall n a b r, PR n a b r) :
    forall n la lb x, All2i_bis_all A B C PC R PR n la lb x :=
    fix f n la lb x : All2i_bis_all A B C PC R PR n la lb x :=
    match x with
    | All2i_bis_nil c => All2i_bis_nil_all c (HPC c)
    | All2i_bis_cons a b lA lB r x => All2i_bis_cons_all a b lA lB r (HPR n a b r) x (f (S n) lA lB x)
    end.

  Register Scheme lfth_All2i_bis_all as local_fundamental_theorem for All2i_bis.

  Inductive triv_All2_bis : Type :=
  | ctriv_All2_bis : All2i_bis bool bool triv_All2_bis (fun _ _ _ => nat) zero (@nil bool) (@nil bool) ->
                    triv_All2_bis.

  (* Scheme SparseParametricity for triv_All2_bis. *)

End Template.

Module UnivPoly.

  (* Example with UnivPoly Inductive Types *)

  Set Universe Polymorphism.

  (* Example with list *)
  Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.

  Arguments nil {_}.
  Arguments cons {_}.

  Infix "::" := cons (at level 60, right associativity) : list_scope.

  Scheme SparseParametricity for list.

  #[universes(polymorphic)]
  Definition lfth_list_all@{sP; uP+} A (PA : A -> Type@{sP;uP}) (HPA : forall pA : A, PA pA) :=
    fix F0_list (x : list A) : list_all A PA x :=
    match x as H return (list_all A PA H) with
    | nil => nil_all A PA
    | cons x0 x1 => cons_all A PA x0 (HPA x0) x1 (F0_list x1)
    end.

  (* register the sparse paremetricity and the local fundamental theorem *)
  Register Scheme lfth_list_all as local_fundamental_theorem for list.

  Inductive MRT : Set :=
  | MRTnode : list MRT -> MRT.

  Inductive RoseTree A : Type :=
  | RTleaf (a : A) : RoseTree A
  | RTnode (l : list (RoseTree A)) : RoseTree A.

  Inductive RoseRoseTree A : Type :=
  | Nleaf (a : A) : RoseRoseTree A
  | Nnode (p : (list (list (RoseRoseTree A)))) : RoseRoseTree A.

  Inductive ArrowTree3 A : Type :=
  | ATleaf3 (a : A) : ArrowTree3 A
  | ATnode3 (l : (bool -> list (nat -> ArrowTree3 A))) : ArrowTree3 A.

  (* Example Prod *)
  Inductive prod (A B : Type) : Type :=
    pair : A -> B -> prod A B.

  Arguments pair {_ _}.

  Scheme SparseParametricity for prod.

  Definition lfth_prod_all@{sa sb ; ua ub +} A (PA : A -> Type@{sa;ua}) (HPA : forall a, PA a)
                        B (PB : B -> Type@{sb|ub}) (HPB : forall b, PB b) :
                        forall (x : prod A B), prod_all A PA B PB x :=
    fun x => match x with
    | pair a b => pair_all A PA B PB a (HPA a) b (HPB b)
    end.

  Register Scheme lfth_prod_all as local_fundamental_theorem for prod.

  Inductive PairTree A : Type :=
  | Pleaf (a : A) : PairTree A
  | Pnode (p : prod (PairTree A) (PairTree A)) : PairTree A.

  Inductive LeftTree A : Type :=
  | Lleaf (a : A) : LeftTree A
  | Lnode (p : prod (LeftTree A) nat) : LeftTree A.

  Inductive RightTree A : Type :=
  | Rleaf (a : A) : RightTree A
  | Rnode (p : prod nat (RightTree A)) : RightTree A.

End UnivPoly.



Module SortPoly.

  (* Example with a sort polymorphic containers *)
  Set Universe Polymorphism.

  Inductive list@{sA;uA uR} (A : Type@{sA;uA}) : Type@{sA; uR} :=
  | nil : list A
  | cons : A -> list A -> list A.

  Arguments nil {_}.
  Arguments cons {_}.

  Infix "::" := cons (at level 60, right associativity) : list_scope.

  Scheme SparseParametricity for list.

  Definition lfth_list_all@{sA sP; uA uP+} (A : Type@{sA; uA}) (PA : A -> Type@{sP;uP}) (HPA : forall pA : A, PA pA) :=
    fix F0_list (x : list A) : list_all A PA x :=
    match x as H return (list_all A PA H) with
    | nil => nil_all A PA
    | cons x0 x1 => cons_all A PA x0 (HPA x0) x1 (F0_list x1)
    end.

  (* register the sparse paremetricity and the local fundamental theorem *)
  Register Scheme lfth_list_all as local_fundamental_theorem for list.

  Inductive MRT : Set :=
  | MRTnode : list MRT -> MRT.

  Inductive SRT : SProp :=
  | SRTnode : list SRT -> SRT.

End SortPoly.

Module TestWarning.

  Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.

  Inductive MRT : Set :=
  | MRTnode : list MRT -> MRT.

End TestWarning.
