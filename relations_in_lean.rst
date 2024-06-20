Relations in Lean
=================

In the last chapter, we noted that set theorists think of a binary relation
:math:`R` on a set :math:`A` as a set of ordered pairs,
so that :math:`R(a, b)` really means :math:`(a, b) \in R`.
An alternative is to think of :math:`R` as a function which,
when applied to :math:`a` and :math:`b`,
returns the proposition that :math:`R(a, b)` holds.
This is the viewpoint adopted by Lean:
a binary relation on a type ``A`` is a function ``A → A → Prop``.
Remember that the arrows associate to the right,
so ``A → A → Prop`` really means ``A → (A → Prop)``.
So, given ``a : A``,
``R a`` is a predicate (the property of being related to ``A``),
and given ``a b : A``, ``R a b`` is a proposition.


Order Relations
---------------

With first-order logic,
we can say what it means for a relation to be reflexive,
symmetric, transitive, antisymmetric, and so on:

.. code-block:: lean

    namespace hidden

    variable {A : Type}

    def Reflexive (R : A → A → Prop) : Prop :=
    ∀ x, R x x

    def Symmetric (R : A → A → Prop) : Prop :=
    ∀ x y, R x y → R y x

    def Transitive (R : A → A → Prop) : Prop :=
    ∀ x y z, R x y → R y z → R x z

    def AntiSymmetric (R : A → A → Prop) : Prop :=
    ∀ x y, R x y → R y x → x = y

    def Irreflexive (R : A → A → Prop) : Prop :=
    ∀ x, ¬ R x x

    def Total (R : A → A → Prop) : Prop :=
    ∀ x y, R x y ∨ R y x

    end hidden

Notice that Lean will unfold the definitions when necessary,
for example, treating ``Reflexive R`` as ``∀ x, R x x``.

.. code-block:: lean

    namespace hidden

    variable {A : Type}

    def Reflexive (R : A → A → Prop) : Prop :=
    ∀ x, R x x

    def Symmetric (R : A → A → Prop) : Prop :=
    ∀ x y, R x y → R y x

    def Transitive (R : A → A → Prop) : Prop :=
    ∀ x y z, R x y → R y z → R x z

    def AntiSymmetric (R : A → A → Prop) : Prop :=
    ∀ x y, R x y → R y x → x = y

    -- BEGIN
    variable (R : A → A → Prop)

    example (h : Reflexive R) (x : A) : R x x := h x

    example (h : Symmetric R) (x y : A) (h1 : R x y) : R y x :=
    h x y h1

    example (h : Transitive R) (x y z : A) (h1 : R x y) (h2 : R y z) :
      R x z :=
    h x y z h1 h2

    example (h : AntiSymmetric R) (x y : A) (h1 : R x y)
        (h2 : R y x) :
      x = y :=
    h x y h1 h2
    -- END

    end hidden

In the command ``variable {A : Type}``,
we put curly braces around ``A`` to indicate that it is an *implicit* argument,
which is to say, you do not have to write it explicitly;
Lean can infer it from the argument ``R``.
That is why we can write ``Reflexive R`` rather than ``Reflexive A R``:
Lean knows that ``R`` is a binary relation on ``A``,
so it can infer that we mean reflexivity for binary relations on ``A``.

Given ``h : Transitive R``, ``h1 : R x y``, and ``h2 : R y z``,
it is annoying to have to write ``h x y z h1 h2`` to prove ``R x z``.
After all,
Lean should be able to infer that we are talking about transitivity at
``x``, ``y``, and ``z``,
from the fact that ``h1`` is ``R x y`` and ``h2`` is ``R y z``.
Indeed, we can replace that information by underscores:

.. code-block:: lean

    namespace hidden

    variable {A : Type}

    def Transitive (R : A → A → Prop) : Prop :=
    ∀ x y z, R x y → R y z → R x z

    -- BEGIN
    variable (R : A → A → Prop)

    example (h : Transitive R) (x y z : A) (h1 : R x y)
        (h2 : R y z) :
      R x z :=
    h _ _ _ h1 h2
    -- END

    end hidden

But typing underscores is annoying, too.
The best solution is to declare the arguments ``x y z``
to a transitivity hypothesis to be implicit as well.
We can do this by introducing curly braces around the
variables in the definition.

.. code-block:: lean

    namespace hidden

    variable {A : Type}

    -- BEGIN
    def Transitive' (R : A → A → Prop) : Prop :=
    ∀ {x} {y} {z}, R x y → R y z → R x z

    def Transitive (R : A → A → Prop) : Prop :=
    ∀ {x y z}, R x y → R y z → R x z

    variable (R : A → A → Prop)

    example (h : Transitive R) (x y z : A) (h1 : R x y)
        (h2 : R y z) :
      R x z :=
    h h1 h2
    -- END

    end hidden

In fact, the notions
``Reflexive``, ``Symmetric``, ``Transitive``,
and so on are defined in Mathlib in exactly this way,
so we are free to use them by doing ``import Mathlib.Init.Logic``
at the top of the file.

.. code:: lean

    import Mathlib.Init.Logic

    #check Reflexive
    #check Symmetric
    #check Transitive
    #check AntiSymmetric
    #check Irreflexive

We put our temporary definitions of in a namespace ``hidden``;
that means that the full name of our version of ``Reflexive`` is
``hidden.Reflexive``,
which would not conflict with the one defined in the library
were we to import that module.

In :numref:`order_relations` we showed that a strict partial order -
that is, a binary relation that is transitive and irreflexive -
is also asymmetric. Here is a proof of that fact in Lean.

.. code-block:: lean

    import Mathlib.Init.Logic

    variable (A : Type)
    variable (R : A → A → Prop)

    -- BEGIN
    example (h1 : Irreflexive R) (h2 : Transitive R) :
        ∀ x y, R x y → ¬ R y x := by
      intro x y
      intro (h3 : R x y)
      intro (h4 : R y x)
      have h5 : R x x := h2 h3 h4
      have h6 : ¬ R x x := h1 x
      show False
      exact h6 h5
    variable A : Type
    variable R : A → A → Prop
    -- END

In mathematics,
it is common to use infix notation and a symbol like ``≼``
to denote a partial order,
which you can input by typing ``\preceq``.
Lean supports this practice:

.. code-block:: lean

    import Mathlib.Init.Logic

    -- BEGIN
    section
    variable (A : Type)
    variable (R : A → A → Prop)

    -- type \preceq for the symbol ≼
    local infix:50 " ≼ " => R

    example (h1 : Irreflexive R) (h2 : Transitive R) :
        ∀ x y, x ≼ y → ¬ y ≼ x := by
      intro x y
      intro (h3 : x ≼ y)
      intro (h4 : y ≼ x)
      have h5 : x ≼ x := h2 h3 h4
      have h6 : ¬ x ≼ x := h1 x
      show False
      exact h6 h5

    end
    -- END

The structure of a partial order consists of a type ``A``
(traditionally a set ``A``)
with a binary relation ``le : A → A → Prop``
(short for "lesser or equal")
on it that is reflexive,
transitive, and antisymmetric.
We can package this structure as a "class" in Lean.

.. code-block:: lean

    import Mathlib.Order.Basic

    namespace hidden

    -- BEGIN
    class PartialOrder (A : Type u) where
      le : A → A → Prop
      refl : Reflexive le
      trans : Transitive le
      antisymm : ∀ {a b : A}, le a b → le b a → a = b

    -- type \preceq for the symbol ≼
    local infix:50 " ≼ " => PartialOrder.le
    -- END

    end hidden

Assuming we have a type ``A`` that is a partial order,
we can define the corresponding strict partial order ``lt : A → A → Prop``
(short for "lesser than")
and prove that it is,
indeed, a strict order.
We also introduce notation ``≺`` for ``le``,
which you can write by typing ``\prec``.

.. code-block:: lean

    import Mathlib.Tactic.Basic
    import Mathlib.Order.Basic

    namespace hidden

    class PartialOrder (A : Type u) where
      le : A → A → Prop
      refl : Reflexive le
      trans : Transitive le
      antisymm : ∀ {a b : A}, le a b → le b a → a = b

    -- type \preceq for the symbol ≼
    local infix:50 " ≼ " => PartialOrder.le

    -- BEGIN
    namespace PartialOrder
    variable {A : Type} [PartialOrder A]

    def lt (a b : A) : Prop := a ≼ b ∧ a ≠ b

    -- type \prec for the symbol ≺
    local infix:50 " ≺ " => lt

    theorem irrefl_lt (a : A) : ¬ (a ≺ a) := by
      intro (h : a ≺ a)
      have : a ≠ a := And.right h
      have : a = a := rfl
      contradiction

    theorem trans_lt {a b c : A} (h₁ : a ≺ b) (h₂ : b ≺ c) : a ≺ c :=
      have : a ≼ b := And.left h₁
      have : a ≠ b := And.right h₁
      have : b ≼ c := And.left h₂
      have : b ≠ c := And.right h₂
      have : a ≼ c := trans ‹a ≼ b› ‹b ≼ c›
      have : a ≠ c :=
        fun hac : a = c ↦
        have : c ≼ b := by rw [← hac]; assumption
        have : b = c := antisymm ‹b ≼ c› ‹c ≼ b›
        show False from ‹b ≠ c› ‹b = c›
      show a ≺ c from And.intro ‹a ≼ c› ‹a ≠ c›

    end PartialOrder
    -- END
    end hidden

The variable declation ``[PartialOrder A]`` can be read as
"assume ``A`` is a partial order".
Then Lean will use this "instance" of the class ``PartialOrder``
to figure out what ``le`` and ``lt`` are referring to.

The proofs use anonymous ``have``,
referring back to them with the French quotes, ```\f<`` and ``\f>``,
or ``assumption`` (in tactic mode).
The proof of transitivity switches from term mode to tactic mode,
to use ``rewrite`` to replace ``c`` for ``a`` in ``a ≤ b``.
Recall that ``contradiction`` intructs Lean to find
a hypothesis and its negation in the context, and hence complete the proof.

We could even define the class ``StrictPartialOrder`` in a similar manner,
then use the above theorems to show that any (weak) ``PartialOrder`` is also a
``StrictPartialOrder``.

.. code-block:: lean

    import Mathlib.Tactic.Basic
    import Mathlib.Order.Basic

    namespace hidden

    class PartialOrder (A : Type u) where
      le : A → A → Prop
      refl : Reflexive le
      trans : Transitive le
      antisymm : ∀ {a b : A}, le a b → le b a → a = b

    -- type \preceq for the symbol ≼
    local infix:50 " ≼ " => PartialOrder.le

    namespace PartialOrder
    variable {A : Type} [PartialOrder A]

    def lt (a b : A) : Prop := a ≼ b ∧ a ≠ b

    -- type \prec for the symbol ≺
    local infix:50 " ≺ " => PartialOrder.lt

    theorem irrefl_lt (a : A) : ¬ (a ≺ a) := by
      intro (h : a ≺ a)
      have : a ≠ a := And.right h
      have : a = a := rfl
      contradiction

    theorem trans_lt {a b c : A} (h₁ : a ≺ b) (h₂ : b ≺ c) : a ≺ c :=
      have : a ≼ b := And.left h₁
      have : a ≠ b := And.right h₁
      have : b ≼ c := And.left h₂
      have : b ≠ c := And.right h₂
      have : a ≼ c := trans ‹a ≼ b› ‹b ≼ c›
      have : a ≠ c :=
        fun hac : a = c ↦
        have : c ≼ b := by rw [← hac]; assumption
        have : b = c := antisymm ‹b ≼ c› ‹c ≼ b›
        show False from ‹b ≠ c› ‹b = c›
      show a ≺ c from And.intro ‹a ≼ c› ‹a ≠ c›

    end PartialOrder

    -- BEGIN
    class StrictPartialOrder (A : Type u) where
      lt : A → A → Prop
      irrefl : Irreflexive lt
      trans : Transitive lt

    -- type \prec for the symbol ≺
    local infix:50 " ≺ " => StrictPartialOrder.lt

    instance {A : Type} [PartialOrder A] : StrictPartialOrder A where
      lt          := PartialOrder.lt
      irrefl      := PartialOrder.irrefl_lt
      trans _ _ _ := PartialOrder.trans_lt

    example (a : A) [PartialOrder A] : ¬ a ≺ a :=
    StrictPartialOrder.irrefl a
    -- END

    end hidden

Once we have shown this instance, we would be able to use the inherited
``≺`` (not the one we defined in the ``PartialOrder`` namespace!)
and facts about ``StrictPartialOrder`` on any partial order.

In Section :numref:`order_relations`,
we also noted that you can define a (weak) partial order from a strict one.
We ask you to do this formally in the exercises below.

Mathlib defines ``PartialOrder`` in roughly the same way as we have,
which is why we enclosed our definitions in the ``hidden`` namespace,
so that our definition is called ``hidden.PartialOrder``
rather than just ``PartialOrder`` outside the namespace.
There is no ``StrictPartialOrder`` definition,
but we can refer to the strict partial order, given a partial order.
The notation used by Mathlib is the more common ``≤``
(input ``\le``) and ``<``.

Here is one more example. Suppose ``R`` is a binary relation on a type ``A``, and we define ``S x y`` to mean that both ``R x y`` and ``R y x`` holds. Below we show that the resulting relation is reflexive and symmetric.

.. code-block:: lean

    section
    axiom A : Type
    axiom R : A → A → Prop

    variable (h1 : Transitive R)
    variable (h2 : Reflexive R)

    def S (x y : A) := R x y ∧ R y x

    example : Reflexive S :=
    fun x ↦
      have : R x x := h2 x
      show S x x from And.intro this this

    example : Symmetric S :=
    fun x y ↦
    fun h : S x y ↦
    have h1 : R x y := h.left
    have h2 : R y x := h.right
    show S y x from ⟨h2, h1⟩

    end

In the exercises below, we ask you to show that ``S`` is transitive as well.

In the first example,
we use the anonymous ``have``,
and then refer back to the ``have`` with the keyword ``this``.
In the second example,
we abbreviate ``And.left h`` and ``And.right h`` as ``h.left`` and ``h.right``,
respectively.
We also abbreviate ``And.intro h2 h1`` with an anonymous constructor,
writing ``⟨h2, h1⟩``.
Lean figures out that we are trying to prove a conjunction,
and figures out that ``And.intro`` is the relevant introduction principle.
You can type the corner brackets with ``\<`` and ``\>``, respectively.

Orderings on Numbers
--------------------

Conveniently,
Lean has the normal orderings on the natural numbers, integers,
and so on defined already in Mathlib.

.. code-block:: lean

    import Mathlib.Data.Nat.Defs

    open Nat
    variable (n m : ℕ)

    #check 0 ≤ n
    #check n < n + 1

    example : 0 ≤ n := Nat.zero_le n
    example : n < n + 1 := lt_succ_self n

    example (h : n + 1 ≤ m) : n < m + 1 :=
    have h1 : n < n + 1 := lt_succ_self n
    have h2 : n < m := lt_of_lt_of_le h1 h
    have h3 : m < m + 1 := lt_succ_self m
    show n < m + 1 from lt_trans h2 h3

There are many theorems in Lean that are useful for proving facts about inequality relations. We list some common ones here.

.. code-block:: lean

    import Mathlib.Order.Basic

    variable (A : Type) [PartialOrder A]
    variable (a b c : A)

    #check (le_trans : a ≤ b → b ≤ c → a ≤ c)
    #check (lt_trans : a < b → b < c → a < c)
    #check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
    #check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
    #check (le_of_lt : a < b → a ≤ b)

Notice that we assume an instance of ``PartialOrder`` on ``A``.
There are also properties that are specific to some domains,
like the natural numbers:

.. code-block:: lean

    import Mathlib.Data.Nat.Defs

    variable (n : ℕ)

    #check (Nat.zero_le : ∀ n : ℕ, 0 ≤ n)
    #check (Nat.lt_succ_self : ∀ n : ℕ, n < n + 1)
    #check (Nat.le_succ : ∀ n : ℕ, n ≤ n + 1)

.. TODO(Jeremy): add a section on equivalence relations


Equivalence Relations
---------------------

In :numref:`equivalence_relations_and_equality` we saw that an *equivalence relation* is a binary relation on some domain :math:`A` that is reflexive, symmetric, and transitive. We will see such relations in Lean in a moment, but first let's define another kind of relation called a *preorder*, which is a binary relation that is reflexive and transitive.
Again, we use a ``class`` to capture this data.

.. code-block:: lean

    import Mathlib.Order.Basic

    namespace hidden

    variable {A : Type}

    class Preorder (A : Type u) where
      le : A → A → Prop
      refl : Reflexive le
      trans : Transitive le

    end hidden

Lean's library provides its own formulation of preorders.
In order to use the same name, we have to put it in the ``hidden`` namespace.
Lean's library defines other properties of relations, such as these:

Building on our definition of a preorder,
we can describe partial orders as antisymmetric preorders,
and equivalences as symmetric preorders.

.. code-block:: lean

    import Mathlib.Order.Basic

    namespace hidden

    variable {A : Type}

    class Preorder (A : Type u) where
      le : A → A → Prop
      refl : Reflexive le
      trans : Transitive le

    class PartialOrder (A : Type u) extends Preorder A where
      antisymm : AntiSymmetric le

   class Equivalence (A : Type u) extends Preorder A where
     symm : Symmetric le

    end hidden

The ``extends Preorder A`` in this definition now makes
``PartialOrder`` a class that automatically
inherits all the definitions and theorems from ``Preorder``.
In particular ``le``, ``refl``, and ``trans`` become part of the data of
``PartialOrder``.
Using classes in this way we can write very general proofs
(for example proofs just about preorders)
and apply them in contexts that are more specific
(for example proofs about equivalence relations and partial orders).

Note: we might *not* want to design the library in this way specifically.
Since we might want to use ``≤`` as notation for a partial order,
but for an equivalence relation.
Indeed ``Mathlib`` does not define ``Equivalence`` as an extension of
``PartialOrder``.

In :numref:`equivalence_relations_and_equality` we claimed that there is
another way to define an equivalence relation,
namely as a binary relation satisfying the following two properties:

-  :math:`\forall a \; (a \equiv a)`
-  :math:`\forall {a, b, c} \; (a \equiv b \wedge c \equiv b \to a \equiv c)`

We derive the two definitions from each other in the following

.. code-block:: lean

    import Mathlib.Order.Basic

    namespace hidden

    class Equivalence (A : Type u) where
      R : A → A → Prop
      refl : Reflexive R
      symm : Symmetric R
      trans : Transitive R

    local infix:50 " ~ " => Equivalence.R

    class Equivalence' (A : Type u) where
      R : A → A → Prop
      refl : Reflexive R
      trans' : ∀ {a b c}, R a b → R c b → R a c

    -- type ``≈`` as ``\~~``
    local infix:50 " ≈ " => Equivalence'.R

    section
    variable {A : Type u}

    theorem Equivalence.trans' [Equivalence A] {a b c : A} :
        a ~ b → c ~ b → a ~ c := by
      intro (hab : a ~ b)
      intro (hcb : c ~ b)
      apply trans hab
      show b ~ c
      exact symm hcb

    example [Equivalence A] : Equivalence' A where
      R := Equivalence.R
      refl := Equivalence.refl
      trans':= Equivalence.trans'

    theorem Equivalence'.symm [Equivalence' A] {a b : A} :
        a ≈ b → b ≈ a := by
      intro (hab : a ≈ b)
      have hbb : b ≈ b := Equivalence'.refl b
      show b ≈ a
      exact Equivalence'.trans' hbb hab

    theorem Equivalence'.trans [Equivalence' A] {a b c : A} :
      a ≈ b → b ≈ c → a ≈ c := by
      intro (hab : a ≈ b) (hbc : b ≈ c)
      have hcb : c ≈ b := Equivalence'.symm hbc
      show a ≈ c
      exact Equivalence'.trans' hab hcb

   example [Equivalence' A] : Equivalence A where
     R := Equivalence'.R
     refl := Equivalence'.refl
     symm _ _:= Equivalence'.symm
     trans _ _ _ := Equivalence'.trans

    end
    end hidden

For one of the definitions we use the infix notation ``~`` and we use
``≈`` for the other. (You can type ``≈`` as ``\~~``.)
We use ``example`` instead of ``instance`` so that we don't actually
instantiate instances of the classes.


Exercises
---------

#. Replace the ``sorry`` commands in the following proofs to show that we can
   create a partial order ``R'​`` out of a strict partial order ``R``.

   .. code-block:: lean

        import Mathlib.Order.Basic

        class StrictPartialOrder (A : Type u) where
          lt : A → A → Prop
          irrefl : Irreflexive lt
          trans : Transitive lt

        local infix:50 " ≺ " => StrictPartialOrder.lt

        section
        variable {A : Type u} [StrictPartialOrder A]

        def R' (a b : A) : Prop :=
        (a ≺ b) ∨ a = b

        local infix:50 " ≼ " => R'

        theorem reflR' (a : A) : a ≼ a := sorry

        theorem transR' {a b c : A} (h1 : a ≼ b) (h2 : b ≼ c) :
          a ≼ c :=
        sorry

        theorem antisymmR' {a b : A} (h1 : a ≼ b) (h2 : b ≼ a) :
          a = b :=
        sorry

        end

#. Replace the ``sorry`` by a proof.

   .. code-block:: lean

        import Mathlib.Order.Basic

        namespace hidden
        class Preorder (A : Type u) where
            le : A → A → Prop
            refl : Reflexive le
            trans : Transitive le

        namespace Preorder
        def S (a b : A) [Preorder A] : Prop := le a b ∧ le b a

        example (A : Type u) [Preorder A] {x y z : A} :
          S x y → S y z → S x z :=
        sorry

        end Preorder
        end hidden

#. Only one of the following two theorems is provable. Figure out which one is true, and replace the ``sorry`` command with a complete proof.

   .. code-block:: lean

         import Mathlib.Order.Basic

         axiom A : Type
         axiom a : A
         axiom b : A
         axiom c : A
         axiom R : A → A → Prop
         axiom Rab : R a b
         axiom Rbc : R b c
         axiom nRac : ¬ R a c

         -- Prove one of the following two theorems:

         theorem R_is_strict_partial_order :
           Irreflexive R ∧ Transitive R :=
         sorry

         theorem R_is_not_strict_partial_order :
           ¬(Irreflexive R ∧ Transitive R) :=
         sorry

#. Complete the following proof. You may use results from Mathlib.

   .. code-block:: lean

    import Mathlib.Data.Nat.Defs

    section
    open Nat
    variable (n m : ℕ)

    example : 1 ≤ 4 :=
    sorry

    end
