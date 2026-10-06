.. this should be just "_program", but refs to it don't work

.. _programs:

Program
========

:Author: Matthieu Sozeau

We present here the |Program| tactic commands, used to build
certified Rocq programs, elaborating them from their algorithmic
skeleton and a rich specification :cite:`sozeau06`. It can be thought of as a
dual of :ref:`Extraction <extraction>`. The goal of |Program| is to
program as in a regular functional programming language whilst using
as rich a specification as desired and proving that the code meets the
specification using the whole Rocq proof apparatus. This is done using
a technique originating from the “Predicate subtyping” mechanism of
PVS :cite:`Rushby98`, which generates type checking conditions while typing a
term constrained to a particular type. Here we insert existential
variables in the term, which must be filled with proofs to get a
complete Rocq term. |Program| replaces the |Program| tactic by Catherine
Parent :cite:`Parent95b` which had a similar goal but is no longer maintained.

The languages available as input is Rocq's term language.
We use the same syntax as Rocq and permit to use
implicit arguments and the existing coercion mechanism. Input terms
and types are typed in an extended system (Russell) and elaborated
into Rocq terms. The elaboration process may produce some proof
obligations which need to be resolved to create the final term.


.. _elaborating-programs:

Elaborating programs
--------------------

The main difference from plain Rocq is that an object in a type :g:`T : Set` can
be considered as an object of type :g:`{x : T | P}` for any well-formed
:g:`P : Prop`. If we go from :g:`T` to the subset of :g:`T` verifying property
:g:`P`, we must prove that the object under consideration verifies it. Russell
will generate an obligation for every such coercion. In the other direction,
Russell will automatically insert a projection.

Another distinction is the treatment of pattern matching. Apart from
the following differences, it is equivalent to the standard match
operation (see :ref:`extendedpatternmatching`).


+ Generation of equalities. A match expression is always generalized
  by the corresponding equality. As an example, the expression:

  ::

   match x with
   | 0 => t
   | S n => u
   end.

  will be first rewritten to:

  ::

   (match x as y return (x = y -> _) with
   | 0 => fun H : x = 0 -> t
   | S n => fun H : x = S n -> u
   end) (eq_refl x).

  This permits to get the proper equalities in the context of proof
  obligations inside clauses, without which reasoning is very limited.

+ Generation of disequalities. If a pattern intersects with a previous
  one, a disequality is added in the context of the second branch. See
  for example the definition of div2 below, where the second branch is
  typed in a context where :g:`∀ p, _ <> S (S p)`.
+ Coercion. If the object being matched is coercible to an inductive
  type, the corresponding coercion will be automatically inserted. This
  also works with the previous mechanism.


There are flags to control the generation of equalities and
coercions.

.. flag:: Program Cases

   This :term:`flag` controls the special treatment of pattern matching generating equalities
   and disequalities when using |Program| (it is on by default). All
   pattern-matches and let-patterns are handled using the standard algorithm
   of Rocq (see :ref:`extendedpatternmatching`) when this flag is
   deactivated.

.. flag:: Program Generalized Coercion

   This :term:`flag` controls the coercion of general inductive types when using |Program|
   (the flag is on by default). Coercion of subset types and pairs is still
   active in this case.

.. flag:: Program Mode

   This :term:`flag` enables the program mode, in which 1) typechecking allows subset coercions and
   2) the elaboration of pattern matching of :cmd:`Fixpoint` and
   :cmd:`Definition` acts as if the :attr:`program` attribute has been
   used, generating obligations if there are unresolved holes after
   typechecking.

.. attr:: program{? = {| yes | no } }
   :name: program; Program

   This :term:`boolean attribute` allows using or disabling the Program mode on a specific
   definition.  An alternative and commonly used syntax is to use the legacy ``Program``
   prefix (cf. :n:`@legacy_attr`) as it is elsewhere in this chapter.

.. _syntactic_control:

Syntactic control over equalities
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

To give more control over the generation of equalities, the
type checker will fall back directly to Coq’s usual typing of dependent
pattern matching if a ``return`` or ``in`` clause is specified. Likewise, the
if construct is not treated specially by |Program| so boolean tests in
the code are not automatically reflected in the obligations. One can
use the :g:`dec` combinator to get the correct hypotheses as in:

.. rocqtop:: in

   From Corelib.Program Require Import Basics Tactics.

.. rocqtop:: all

   Program Definition id (n : nat) : { x : nat | x = n } :=
     if sumbool_of_bool (Nat.leb n 0) is left _ then 0
     else S (pred n).

The :g:`let` tupling construct :g:`let (x1, ..., xn) := t in b` does not
produce an equality, contrary to the let pattern construct
:g:`let '(x1,..., xn) := t in b`.

The next two commands are similar to their standard counterparts
:cmd:`Definition` and :cmd:`Fixpoint`
in that they define :term:`constants <constant>`. However, they may require the user to
prove some goals to construct the final definitions.


.. _program_definition:

Program Definition
~~~~~~~~~~~~~~~~~~

A :cmd:`Definition` command with the :attr:`program` attribute types
the value term in Russell and generates proof
obligations. Once solved using the commands shown below, it binds the
final Rocq term to the name :n:`@ident` in the global environment.

:n:`Program Definition @ident_decl : @type := @term`

Interprets the type :n:`@type`, potentially generating proof
obligations to be resolved. Once done with them, we have a Rocq
type :n:`@type__0`. It then elaborates the preterm :n:`@term` into a Rocq
term :n:`@term__0`, checking that the type of :n:`@term__0` is coercible to
:n:`@type__0`, and registers :n:`@ident` as being of type :n:`@type__0` once the
set of obligations generated during the interpretation of :n:`@term__0`
and the aforementioned coercion derivation are solved.

.. exn:: Non extensible universe declaration not supported with monomorphic Program Definition.

   The absence of additional universes or constraints cannot be properly enforced even without Program.

.. seealso:: Sections :ref:`controlling-the-reduction-strategies`, :tacn:`unfold`

.. _program_fixpoint:

Program Fixpoint
~~~~~~~~~~~~~~~~

A :cmd:`Fixpoint` command with the :attr:`program` attribute may also generate obligations. It works
with mutually recursive definitions too.  For example:

.. rocqtop:: reset in

   From Corelib.Program Require Import Basics Tactics.

.. rocqtop:: all

   Program Fixpoint div2 (n : nat) : { x : nat | n = 2 * x \/ n = 2 * x + 1 } :=
     match n with
     | S (S p) => S (div2 p)
     | _ => O
     end.

The :cmd:`Fixpoint` command may include an optional :n:`@fixannot` annotation, which can be:

+ :g:`measure f R` where :g:`f` is a value of type :g:`X` computed on
  any subset of the arguments and the optional term
  :g:`R` is a relation on :g:`X`. :g:`X` defaults to :g:`nat` and :g:`R`
  to :g:`lt`.

+ :g:`wf R x` which is equivalent to :g:`measure x R`.

.. todo see https://github.com/rocq-prover/rocq/pull/12936#discussion_r492747830

Here we have one obligation for each branch (branches for :g:`0` and
``(S 0)`` are automatically generated by the pattern matching
compilation algorithm).

.. rocqtop:: all

   Obligation 1.

.. rocqtop:: reset none

   From Corelib.Program Require Import Basics Tactics Wf.

One can use a well-founded order or a measure as termination orders
using the syntax:

.. rocqtop:: in

   Program Fixpoint div2 (n : nat) {measure n} : { x : nat | n = 2 * x \/ n = 2 * x + 1 } :=
     match n with
     | S (S p) => S (div2 p)
     | _ => O
     end.

.. note:: The :g:`measure f R` and :g:`wf R x` annotations add an
   implicit argument to the functions being defined. When the function
   name is prefixed with :g:`@` (see :ref:`deactivation-of-implicit-arguments`),
   the position of the extra argument needs to be taken into account,
   e.g. by providing :g:`_` or an explicit value.

.. caution:: When defining structurally recursive functions, the generated
   obligations should have the prototype of the currently defined
   functional in their context. In this case, the obligations should be
   transparent (e.g. defined using :g:`Defined`) so that the guardedness
   condition on recursive calls can be checked by the kernel’s type-
   checker. There is an optimization in the generation of obligations
   which gets rid of the hypothesis corresponding to the functional when
   it is not necessary, so that the obligation can be declared opaque
   (e.g. using :g:`Qed`). However, as soon as it appears in the context, the
   proof of the obligation is *required* to be declared transparent.

   No such problems arise when using measures or well-founded recursion.

.. rubric:: Well-founded recursion combinators

Both :g:`wf` and :g:`measure` use the same well-founded recursion
infrastructure. For a measure :g:`m` and a relation :g:`R` on its values,
Program uses the relation :g:`MR R m x y := R (m x) (m y)` on the function's
arguments. The default relation for a natural-number measure is :g:`lt`.

The following definitions from :g:`Corelib.Program.Wf` implement this
recursion. Here, :g:`A : Type` is the argument type, :g:`R : A -> A -> Prop`
is the relation, :g:`Rwf : well_founded R` proves its well-foundedness, and
:g:`P : A -> Type` gives the result type. The function body :g:`F_sub` has type
:g:`forall x : A, (forall y : {y : A | R y x}, P (proj1_sig y)) -> P x`;
its second argument supplies recursive results for predecessors of :g:`x`.

With :flag:`Guard Checking Option Traversing Subterm Analysis` enabled,
Program uses :g:`Fix_sub`, which supplies the initial accessibility proof to
:g:`Fix_F_sub`:

.. rocqdoc::

   Fixpoint Fix_F_sub (x : A) (r : Acc R x) : P x :=
     F_sub x (fun y : {y : A | R y x} =>
       Fix_F_sub (proj1_sig y) (Acc_inv r (proj2_sig y))).

   Definition Fix_sub (x : A) := Fix_F_sub x (Rwf x).

The structural argument of :g:`Fix_F_sub` is the accessibility proof :g:`r`.
The recursive call obtains a predecessor's accessibility proof through
:g:`Acc_inv`, whose definition matches :g:`r`. Recognizing its result as a
strict subterm of :g:`r` requires traversing subterm analysis.

With the flag disabled, Program uses :g:`Fix_sub_struct` instead:

.. rocqdoc::

   Fixpoint Fix_F_sub_struct (x : A) (r : Acc R x) {struct r} : P x :=
     match r with
     | Acc_intro _ k =>
       F_sub x (fun y : {y : A | R y x} =>
         Fix_F_sub_struct (proj1_sig y) (k (proj1_sig y) (proj2_sig y)))
     end.

   Definition Fix_sub_struct (x : A) := Fix_F_sub_struct x (Rwf x).

This variant matches :g:`r` before making recursive calls. The match exposes
:g:`k : forall y, R y x -> Acc R y` as a recursive constructor argument of
:g:`r`, so the recursive argument :g:`k (proj1_sig y) (proj2_sig y)` is
accepted without traversing subterm analysis.

Program selects the combinator when the definition is elaborated. Changing
the flag later does not change this choice for existing definitions or their
pending obligations.

The alternative combinator may remain blocked during reduction if the
accessibility proof is opaque. Opaque obligations are still accepted;
:g:`fix_sub_struct_eq` and :g:`Fix_sub_struct_rect` support reasoning about
the resulting functions without unfolding the accessibility proof.

.. _program_lemma:

Program Lemma
~~~~~~~~~~~~~

A :cmd:`Lemma` command with the :attr:`program` attribute uses the Russell
language to type statements of logical
properties. It generates obligations, tries to solve them
automatically and fails if some unsolved obligations remain. In this
case, one can first define the lemma’s statement using :cmd:`Definition`
and use it as the goal afterwards. Otherwise the proof
will be started with the elaborated version as a goal. The
:attr:`program` attribute can similarly be used with
:cmd:`Variable`, :cmd:`Hypothesis`, :cmd:`Axiom` etc.

.. _solving_obligations:

Solving obligations
-------------------

The following commands are available to manipulate obligations. The
optional identifier is used when multiple functions have unsolved
obligations (e.g. when defining mutually recursive blocks). The
optional tactic is replaced by the default one if not specified.

.. cmd:: Obligation Tactic := @generic_tactic

   Sets the default obligation solving tactic applied to all obligations
   automatically, whether to solve them or when starting to prove one,
   e.g. using :cmd:`Next Obligation`.

   This command supports the :attr:`local`, :attr:`export` and :attr:`global` attributes.
   :attr:`local` makes the setting last only for the current
   module. :attr:`local` is the default inside sections while :attr:`global`
   otherwise. :attr:`export` and :attr:`global` may be used together.

   When :attr:`global` is used without :attr:`export` and when no
   explicit locality is used outside sections, the meaning is
   different from the usual meaning of :attr:`global`: the command's
   effect persists after the current module is closed (as with the
   usual :attr:`global`), but it is also reapplied when the module or
   any of its parents is imported. This will change in a future
   version.

.. cmd:: Show Obligation Tactic

   Displays the current default tactic.

.. cmd:: Obligations {? of @ident }

   Displays all remaining obligations.

.. cmd:: Obligation @natural {? of @ident } {? with @generic_tactic }

   Start the proof of obligation :token:`natural`.

.. cmd:: Next Obligation {? of @ident } {? with @generic_tactic }

   Start the proof of the next unsolved obligation.

.. cmd:: Final Obligation {? of @ident } {? with @generic_tactic }

   Like :cmd:`Next Obligation`, starts the proof of the next unsolved
   obligation. Additionally, at :cmd:`Qed` time, after the
   automatic solver has run on any remaining obligations, Rocq checks
   that no obligations remain for the given :token:`ident` when
   provided and otherwise in the current module.

.. cmd:: Solve Obligations {? of @ident } {? with @ltac_expr }

   Tries to solve each obligation of :token:`ident` using the given :token:`ltac_expr` or the default one.

.. cmd:: Solve All Obligations {? with @ltac_expr }

   Tries to solve each obligation of every program using the given
   tactic or the default one (useful for mutually recursive definitions).

.. cmd:: Admit Obligations {? of @ident }

   Admits all obligations (of :token:`ident`).  Each admitted obligation emits
   the :warn:`admitted-proof` warning when it is enabled.

   .. note:: Does not work with structurally recursive programs.

.. cmd:: Preterm {? of @ident }

   Shows the term that will be fed to the kernel once the obligations
   are solved. Useful for debugging.

.. flag:: Transparent Obligations

   This :term:`flag` controls whether all obligations should be declared as transparent
   (the default), or if the system should infer which obligations can be
   declared opaque.

The module :g:`Corelib.Program.Tactics` defines the default tactic for solving
obligations called :g:`program_simpl`. Importing :g:`Stdlib.Program.Program` also
adds some useful notations, as documented in the file itself.

.. _program-faq:

Frequently Asked Questions
---------------------------


.. exn:: Ill-formed recursive definition.

  This error can happen when one tries to define a function by structural
  recursion on a subset object, which means the Rocq function looks like:

  ::

     Program Fixpoint f (x : A | P) := match x with A b => f b end.

  Supposing ``b : A``, the argument at the recursive call to ``f`` is not a
  direct subterm of ``x`` as ``b`` is wrapped inside an ``exist`` constructor to
  build an object of type ``{x : A | P}``.  Hence the definition is
  rejected by the guardedness condition checker.  However one can use
  wellfounded recursion on subset objects like this:

  ::

     Program Fixpoint f (x : A | P) { measure (size x) } :=
       match x with A b => f b end.

  One will then just have to prove that the measure decreases at each
  recursive call. There are three drawbacks though:

    #. A measure function has to be defined;
    #. The reduction is a little more involved, although it works well
       using lazy evaluation;
    #. Mutual recursion on the underlying inductive type isn’t possible
       anymore, but nested mutual recursion is always possible.
