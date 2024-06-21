Functions in Lean
=================

Functions and Symbolic Logic
----------------------------

Let us now consider functions in formal terms. Even though we have avoided the use of quantifiers and logical symbols in the definitions in the last chapter, by now you should be seeing them lurking beneath the surface. That fact that two functions :math:`f, g : X \to Y` are equal if and only if they take the same values at every input can be expressed as follows:

.. math::

   \forall x \in X \; (f(x) = g(x)) \leftrightarrow f = g .

This principle is a known as *function extensionality*, analogous to the principle of extensionality for sets, discussed in :numref:`sets_in_lean_basics`. Recall that the notation :math:`\forall x \in X \; P(x)` abbreviates :math:`\forall x \; (x \in X \to P(x))`, and :math:`\exists x \in X \; P(x)` abbreviates :math:`\exists x \; (x \in X \wedge P(x))`, thereby relativizing the quantifiers to :math:`X`.

We can avoid set-theoretic notation if we assume we are working in a logical formalism with basic types for :math:`X` and :math:`Y`, so that we can specify that :math:`x` ranges over :math:`X`. In that case, we will write instead

.. math::

   \forall x : X \; (f(x) = g(x) \leftrightarrow f = g)

to indicate that the quantification is over :math:`X`. Henceforth, we will assume that all our variables range over some type, though we will sometimes omit the types in the quantifiers when they can be inferred from context.

The function :math:`f` is injective if it satisfies

.. math::

   \forall x_1, x_2 : X \; (f(x_1) = f(x_2) \to x_1 = x_2),

and :math:`f` is surjective if

.. math::

   \forall y : Y \; \exists x : X \; f(x) = y.

If :math:`f : X \to Y` and :math:`g: Y \to X`, :math:`g` is a left inverse to :math:`f` if

.. math::

   \forall x : X \; g(f(x)) = x.

Notice that this is a universal statement, and it is equivalent to the statement that :math:`f` is a right inverse to :math:`g`.

Remember that in logic it is common to use lambda notation to define functions. We can denote the identity function by :math:`\lambda x \; x`, or perhaps :math:`\lambda x : X \; x` to emphasize that the domain of the function is :math:`X`. If :math:`f : X \to Y` and :math:`g : Y \to Z`, we can define the composition :math:`g \circ f` by :math:`g \circ f = \lambda x : X \; g(f(x))`.

Also remember that if :math:`P(x)` is any predicate, then in first-order logic we can assert that there exists a unique :math:`x` satisfying :math:`P(x)`, written :math:`\exists! x \; P(x)`, with the conjunction of the following two statements:

-  :math:`\exists x \; P(x)`
-  :math:`\forall x_1, x_2 \; (P(x_1) \wedge P(x_2) \to x_1 = x_2)`

Equivalently, we can write

.. math::

   \exists (P(x) \wedge \forall x' \; (P(x') \to x' = x)).

Assuming :math:`\exists! x \; P(x)`, the following two statements are equivalent:

-  :math:`\exists x \; (P(x) \wedge Q(x))`
-  :math:`\forall x \; (P(x) \to Q(x))`

and both can be taken to assert that "the :math:`x` satisfying :math:`P` also satisfies :math:`Q`."

A binary relation :math:`R` on :math:`X` and :math:`Y` is functional if it satisfies

.. math::

   \forall x \; \exists! y \; R(x,y).

In that case, a logician might use *iota notation*,

.. math::

   f(x) = \iota y \; R(x, y)

to define :math:`f(x)` to be equal to the unique :math:`y` satisfying :math:`R(x,y)`. If :math:`R` satisfies the weaker property

.. math::

   \forall x \; \exists y \; R(x,y),

a logician might use the *Hilbert epsilon* to define a function

.. math::

   f(x) = \varepsilon y \; R(x, y)

to "choose" a value of :math:`y` satisfying :math:`R(x, y)`. As we have noted above, this is an implicit use of the axiom of choice.

Second- and Higher-Order Logic
------------------------------

In contrast to first-order logic, where we start with a fixed stock of function and relation symbols, the topics we have been considering in the last few chapters encourage us to consider a more expressive language with variables ranging over functions and relations as well. For example, saying that a function :math:`f : X \to Y` has a left-inverse implicitly involves a quantifying over functions,

.. math::

   \exists g \; \forall x \; g(f(x)) = x.

The theorem that asserts that if any function :math:`f` from :math:`X` to :math:`Y` is injective then it has a left-inverse can be expressed as follows:

.. math::

   \forall x_1, x_2 \; (f(x_1) = f(x_2) \to x_1 = x_2) \to \exists g \; \forall x \; g(f(x)) = x.

Similarly, saying that two sets :math:`X` and :math:`Y` have a one-to-one correspondence asserts the existence of a function :math:`f : X \to Y` as well as an inverse to :math:`f`. For another example, in :numref:`functions_and_relations` we asserted that every functional relation gives rise to a corresponding function, and vice-versa.

What makes these statements interesting is that they involve quantification, both existential and universal, over functions and relations. This takes us outside the realm of first-order logic. One option is to develop a theory in the language of first-order logic in which the universe contains functions and relations as objects; we will see later that this is what axiomatic set theory does. An alternative is to extend first-order logic to involve new kinds of quantifiers and variables, to range over functions and relations. This is what higher-order logic does.

There are various ways to go about this. In view of the relationship between functions and relations described earlier, one can take relations as basic, and define functions in terms of them, or vice-versa. The following formulation of higher-order logic, due to the logician Alonzo Church, follows the latter approach. It is sometimes known as *simple type theory*.

Start with some basic types, :math:`X, Y, Z, \ldots` and a special type, :math:`\mathrm{Prop}`, of propositions. Add the following two rules to build new types:

-  If :math:`U` and :math:`V` are types, so is :math:`U \times V`.
-  If :math:`U` and :math:`V` are types, so is :math:`U \to V`.

The first intended to denote the type of ordered pairs :math:`(u, v)`, where :math:`u` is in :math:`U` and :math:`v` is in :math:`V`. The second is intended to denote the type of functions from :math:`U` to :math:`V`. Simple type theory now adds the following means of forming expressions:

-  If :math:`u` is of type :math:`U` and :math:`v` is of type :math:`V`, :math:`(u, v)` is of type :math:`U \times V`.
-  If :math:`p` is of type :math:`U \times V`, then :math:`(p)_1` is of type :math:`U` and :math:`(p)_2` if of type :math:`V`. (These are intended to denote the first and second element of the pair :math:`p`.)
-  If :math:`x` is a variable of type :math:`U`, and :math:`v` is any expression of type :math:`V`, then :math:`\lambda x \; v` is of type :math:`U \to V`.
-  If :math:`f` is of type :math:`U \to V` and :math:`u` is of type :math:`U`, :math:`f(u)` is of type :math:`V`.

In addition, simple type theory provides all the means we have in first-order logic---boolean connectives, quantifiers, and equality---to build propositions.

A function :math:`f(x, y)` which takes elements of :math:`X` and :math:`Y` to a type :math:`Z` is viewed as an object of type :math:`X \times Y \to Z`. Similarly, a binary relation :math:`R(x,y)` on :math:`X` and :math:`Y` is viewed as an object of type :math:`X \times Y \to \mathrm{Prop}`. What makes higher-order logic "higher order" is that we can iterate the function type operation indefinitely. For example, if :math:`\mathbb{N}` is the type of natural numbers, :math:`\mathbb{N} \to \mathbb{N}` denotes the type of functions from the natural numbers to the natural numbers, and :math:`(\mathbb{N} \to \mathbb{N}) \to \mathbb{N}` denotes the type of functions :math:`F(f)` which take a function as argument, and return a natural number.

We have not specified the syntax and rules of higher-order logic very carefully. This is done in a number of more advanced logic textbooks. The fragment of higher-order logic which allows only functions and relations on the basic types (without iterating these constructions) is known as second-order logic.

These notions should seem familiar; we have been using these constructions, with similar notation, in Lean. Indeed, Lean's logic is an even more elaborate and expressive system of logic, which fully subsumes all the notions of higher-order logic we have discussed here.

Functions in Lean
-----------------

The fact that the notions we have been discussing have such a straightforward logical form means that it is easy to define them in Lean. The main difference between the formal representation in Lean and the informal representation above is that, in Lean, we distinguish between a type ``X`` and a subset
``A : Set X`` of that type.

In Lean's library, composition and identity are defined as follows:

.. code-block:: lean

    namespace hidden
    -- BEGIN
    variable {X Y Z : Type}

    def comp (f : Y → Z) (g : X → Y) : X → Z :=
    fun x ↦ f (g x)

    infixr:50 " ∘ " => comp

    def id (x : X) : X :=
    x
    -- END
    end hidden

Ordinarily, we use ``funext`` (for "function extensionality") to prove that two functions are equal.

.. code-block:: lean

    variable {X Y : Type}

    -- BEGIN
    example (f g : X → Y) (h : ∀ x, f x = g x) : f = g :=
    funext h
    -- END

But Lean can prove some basic identities by simply unfolding definitions and simplifying expressions, using reflexivity.

.. code-block:: lean

    import Mathlib.Tactic.Basic

    open Function
    variable {X Y Z W : Type}

    -- BEGIN
    lemma left_id (f : X → Y) : id ∘ f = f := rfl

    lemma right_id (f : X → Y) : f ∘ id = f := rfl

    theorem comp.assoc (f : Z → W) (g : Y → Z) (h : X → Y) :
      (f ∘ g) ∘ h = f ∘ (g ∘ h) := rfl

    theorem comp.left_id (f : X → Y) : id ∘ f = f := rfl

    theorem comp.right_id (f : X → Y) : f ∘ id = f := rfl
    -- END

We can define what it means for :math:`f` to be injective, surjective, or bijective:

.. code-block:: lean

    variable {X Y Z : Type}

    -- BEGIN
    def Injective (f : X → Y) : Prop :=
    ∀ ⦃x₁ x₂⦄, f x₁ = f x₂ → x₁ = x₂

    def Surjective (f : X → Y) : Prop :=
    ∀ y, ∃ x, f x = y

    def Bijective (f : X → Y) := Injective f ∧ Surjective f
    -- END

Marking the variables ``x₁`` and ``x₂`` implicit in the definition of ``Injective`` means that we do not have to write them as often. Specifically, given ``h : Injective f``, and ``h₁ : f x₁ = f x₂``, we write ``h h₁`` rather than ``h x₁ x₂ h₁`` to show ``x₁ = x₂``.

We can then prove that the identity function is bijective:

.. code-block:: lean

    import Mathlib.Init.Function
    open Function

    namespace hidden
    variable {X Y Z : Type}

    -- BEGIN
    theorem injective_id : Injective (@id X) :=
    fun x₁ x₂ ↦
    fun H : id x₁ = id x₂ ↦
    show x₁ = x₂ from H

    theorem surjective_id : Surjective (@id X) :=
    fun y ↦
    show ∃ x, id x = y from Exists.intro y rfl

    theorem bijective_id : Bijective (@id X) :=
    And.intro injective_id surjective_id
    -- END

    end hidden

More interestingly, we can prove that the composition of injective functions is injective, and so on.

.. code-block:: lean

    import Mathlib.Init.Function
    open Function

    namespace hidden
    variable {X Y Z : Type}

    -- BEGIN
    theorem Injective.comp {g : Y → Z} {f : X → Y}
        (Hg : Injective g) (Hf : Injective f) :
      Injective (g ∘ f) := by
      intro x₁ x₂ (h : (g ∘ f) x₁ = (g ∘ f) x₂)
      have : f x₁ = f x₂ := Hg h
      show x₁ = x₂
      exact Hf this

    theorem Surjective.comp {g : Y → Z} {f : X → Y}
        (hg : Surjective g) (hf : Surjective f) :
      Surjective (g ∘ f) := by
      intro z
      cases hg z with
      | intro y hy =>
        cases hf y with
        | intro x hx =>
          show ∃ a, (g ∘ f) a = z
          rw [← hy, ← hx]
          show ∃ a, (g ∘ f) a = g (f x)
          exact ⟨x, rfl⟩

    theorem Bijective.comp {g : Y → Z} {f : X → Y}
        (hg : Bijective g) (hf : Bijective f) :
      Bijective (g ∘ f) :=
    have gInj : Injective g := hg.left
    have gSurj : Surjective g := hg.right
    have fInj : Injective f := hf.left
    have fSurj : Surjective f := hf.right
    And.intro (injective_comp gInj fInj)
      (surjective_comp gSurj fSurj)
    -- END

    end hidden

The notions of left and right inverse are defined in the expected way.

.. code-block:: lean

    variable {X Y : Type}

    namespace hidden

    -- BEGIN
    -- g is a left inverse to f
    def LeftInverse (g : Y → X) (f : X → Y) : Prop :=
    ∀ x, g (f x) = x

    -- g is a right inverse to f
    def RightInverse (g : Y → X) (f : X → Y) : Prop :=
    LeftInverse f g
    -- END

    end hidden

In particular, composing with a left or right inverse yields the identity.

.. code-block:: lean

    import Mathlib.Init.Function

    open Function
    section
    variable {X Y Z : Type}

    -- BEGIN
    def LeftInverse.comp_eq_id {g : Y → X} {f : X → Y} :
      LeftInverse g f → g ∘ f = id :=
    fun H ↦ funext H

    def RightInverse.comp_eq_id {g : Y → X} {f : X → Y} :
      RightInverse g f → f ∘ g = id :=
    fun H ↦ funext H
    -- END

    end

Notice that we need to use ``funext`` to show the equality of functions.

The following shows that if a function has a left inverse, then it is injective, and if it has a right inverse, then it is surjective.

.. code-block:: lean

    import Mathlib.Init.Function

    open Function
    variable {X Y : Type}

    namespace hidden
    -- BEGIN
    theorem LeftInverse.injective {g : Y → X} {f : X → Y} :
      LeftInverse g f → Injective f := by
      intro h x₁ x₂ feq
      calc x₁ = g (f x₁) := by rw [h]
            _ = g (f x₂) := by rw [feq]
            _ = x₂       := by rw [h]

    theorem RightInverse.surjective {g : Y  → X} {f : X → Y} :
      RightInverse g f → Surjective f :=
      fun h y ↦
      let x : X := g y
      have : f x = y :=
        calc
          f x  = (f (g y)) := by rfl
             _ = y         := by rw [h y]
      show ∃ x, f x = y from Exists.intro x this
    -- END

    end hidden

Note that like ``have``,
we used the command ``let`` to define an intermediate term.
The difference is that ``have`` is used for proof terms only (of type ``Prop``),
but ``let`` can be used for any term.


Defining the Inverse Classically
--------------------------------

All the theorems listed in the previous section are found in the Lean
library, and are available to you when you
import ``Mathlib.Init.Function`` and open the function namespace
with ``open Function``:

.. code-block:: lean

    import Mathlib.Init.Function
    open Function

    #check comp
    #check LeftInverse
    #check HasRightInverse

Defining inverse functions, however, requires classical reasoning, which
we get by opening the classical namespace:

.. code-block:: lean

    import Mathlib.Init.Function
    open Classical

    section
      variable (A B : Type)
      variable (P : A → Prop)
      variable (R : A → B → Prop)

      example : (∀ x, ∃ y, R x y) → ∃ f : A → B, ∀ x, R x (f x) :=
      axiomOfChoice

      example (h : ∃ x, P x) : P (choose h) :=
      choose_spec h
    end

The axiom of choice tells us that if, for every ``x : X``,
there is a ``y : Y`` satisfying ``R x y``,
then there is a function ``f : X → Y`` which,
for every ``x`` chooses such a ``y``.
In Lean, this "axiom" is proved using a classical construction,
the ``choose`` function
(sometimes called "the indefinite description operator") which,
given that there is some choice ``x`` satisfying ``P x``,
returns such an ``x``.
With these constructions, the inverse function is defined as follows:

.. code-block:: lean

    import Mathlib.Init.Function
    open Classical Function

    variable {X Y : Type}

    noncomputable def inverse (f : X → Y) (default : X) : Y → X :=
    fun y ↦ if h : ∃ x, f x = y then choose h else default

Lean requires us to acknowledge that the definition is not computational, since, first, it may not be algorithmically possible to decide whether or not condition ``h`` holds, and even if it does, it may not be algorithmically possible to find a suitable value of ``x``.

Below, the proposition ``inverse_of_exists`` asserts that ``inverse`` meets its specification, and the subsequent theorem shows that if ``f`` is injective, then the ``inverse`` function really is a left inverse.

.. code-block:: lean

    import Mathlib.Init.Function
    open Classical Function

    variable {X Y : Type}

    noncomputable def inverse (f : X → Y) (default : X) : Y → X :=
    fun y ↦ if h : ∃ x, f x = y then choose h else default

    -- BEGIN
    theorem inverse_of_exists (f : X → Y) (default : X) (y : Y)
        (h : ∃ x, f x = y) :
      f (inverse f default y) = y := by
      have h1 : inverse f default y = choose h := dif_pos h
      have h2 : f (choose h) = y := choose_spec h
      rw [h1, h2]

    theorem is_left_inverse_of_injective (f : X → Y) (default : X)
      (injf : Injective f) :
    LeftInverse (inverse f default) f :=
      let finv := (inverse f default)
      fun x ↦
      have h1 : ∃ x', f x' = f x := Exists.intro x rfl
      have h2 : f (finv (f x)) = f x := inverse_of_exists f default (f x) h1
      show finv (f x) = x from injf h2
    -- END

Functions and Sets in Lean
--------------------------

In :numref:`relativization_and_sorts` we saw how to represent relativized universal and existential quantifiers when formalizing phrases like "every prime number greater than two is odd" and "some prime number is even." In a similar way, we can relativize statements to sets. In symbolic logic, the expression :math:`\exists x \in A \; P (x)` abbreviates :math:`\exists x \; (x \in A \wedge P(x))`, and :math:`\forall x \in A \; P (x)` abbreviates :math:`\forall x \; (x \in A \to P(x))`.

Lean also defines notation for relativized quantifiers:

.. code-block:: lean

    variable (X : Type) (A : Set X) (P : X → Prop)

    #check ∀ x ∈ A, P x
    #check ∃ x ∈ A, P x

Here is an example of how to use the bounded universal quantifier:

.. code-block:: lean

    variable (X : Type) (A : Set X) (P : X → Prop)

    -- BEGIN
    example (h : ∀ x ∈ A, P x) (x : X) (h1 : x ∈ A) : P x := h x h1
    -- END

Using bounded quantifiers, we can talk about the behavior of functions on particular sets:

.. code-block:: lean

    import Mathlib.Data.Set.Basic
    open Set Function

    variable {X Y : Type}
    variable (A  : Set X) (B : Set Y)

    def MapsTo (f : X → Y) (A : Set X) (B : Set Y) :=
      ∀ {x}, x ∈ A → f x ∈ B

    def InjOn (f : X → Y) (A : Set X) :=
      ∀ {x₁ x₂}, x₁ ∈ A → x₂ ∈ A → f x₁ = f x₂ → x₁ = x₂

    def SurjOn (f : X → Y) (A : Set X) (B : Set Y) := B ⊆ f '' A

The expression ``MapsTo f A B`` asserts that ``f`` maps elements of the set ``A`` to the set ``B``, and the expression ``InjOn f A`` asserts that ``f`` is injective on ``A``. The expression ``SurjOn f A B`` asserts that, viewed as a function defined on elements of ``A``, the function ``f`` is surjective onto the set ``B``. Here are examples of how they can be used:

.. code-block:: lean

    import Mathlib.Data.Set.Basic
    open Set Function

    variable {X Y : Type}

    -- BEGIN
    variable (f : X → Y) (A : Set X) (B : Set Y)

    example (h : MapsTo f A B) (x : X) (h1 : x ∈ A) : f x ∈ B := h h1

    example (h : InjOn f A) (x₁ x₂ : X) (h1 : x₁ ∈ A) (h2 : x₂ ∈ A)
        (h3 : f x₁ = f x₂) : x₁ = x₂ :=
    h h1 h2 h3
    -- END

In the examples below, we'll use the versions with implicit arguments. The expression ``SurjOn f A B`` asserts that, viewed as a function defined on elements of ``A``, the function ``f`` is surjective onto the set ``B``.

With these notions in hand, we can prove that the composition of injective functions is injective. The proof is similar to the one above, though now we have to be more careful to relativize claims to ``A`` and ``B``:

.. code-block:: lean

    import Mathlib.Data.Set.Function
    open Set Function

    variable {X Y Z : Type}
    variable (A : Set X) (B : Set Y)
    variable (f : X → Y) (g : Y → Z)

    -- BEGIN
    theorem InjOn.comp (fAB : MapsTo f A B) (hg : InjOn g B) (hf: InjOn f A) :
      InjOn (g ∘ f) A := by
      intro (x1 : X)
      intro (x1A : x1 ∈ A)
      intro (x2 : X)
      intro (x2A : x2 ∈ A)
      have fx1B : f x1 ∈ B := fAB x1A
      have fx2B : f x2 ∈ B := fAB x2A
      intro (h1 : g (f x1) = g (f x2))
      have h2 : f x1 = f x2 := hg fx1B fx2B h1
      show x1 = x2
      exact hf x1A x2A h2
    -- END

We can similarly prove that the composition of surjective functions is surjective:

.. code-block:: lean

    import Mathlib.Data.Set.Function
    open Set Function

    variable {X Y Z : Type}
    variable (A : Set X) (B : Set Y)
    variable (f : X → Y) (g : Y → Z)

    -- BEGIN
    theorem SurjOn.comp (hg : SurjOn g B C) (hf: SurjOn f A B) :
      SurjOn (g ∘ f) A C := by
    intro z
    intro (zc : z ∈ C)
    cases hg zc with
    | intro y h1 => cases hf (h1.left) with
      | intro x h2 =>
        show ∃x, x ∈ A ∧ g (f x) = z
        apply Exists.intro x
        apply And.intro h2.left
        show g (f x) = z
        rw [h2.right]
        show g y = z
        exact h1.right
    -- END

The following shows that the image of a union is the union of images:

.. code-block:: lean

  import Mathlib.Data.Set.Function
  open Set Function

  variable {X Y : Type}
  variable (A₁ A₂ : Set X)
  variable (f : X → Y)

  -- BEGIN
  theorem image_union : f '' (A₁ ∪ A₂) = f '' A₁ ∪ f '' A₂ := by
    ext y
    constructor
    . intro (h : y ∈ image f (A₁ ∪ A₂))
      cases h with
      | intro x hx =>
        have xA₁A₂ : x ∈ A₁ ∪ A₂ := hx.left
        have fxy : f x = y := hx.right
        cases xA₁A₂ with
        | inl xA₁ => exact Or.inl ⟨x, xA₁, fxy⟩
        | inr xA₂ => exact Or.inr ⟨x, xA₂, fxy⟩
    . intro (h : y ∈ image f A₁ ∪ image f A₂)
      cases h with
      | inl yifA₁ =>
        cases yifA₁ with
        | intro x hx =>
          have xA₁ : x ∈ A₁ := hx.left
          have fxy : f x = y := hx.right
          exact ⟨x, Or.inl xA₁, fxy⟩
      | inr yifA₂ => cases yifA₂ with
        | intro x hx =>
          have xA₂ : x ∈ A₂ := hx.left
          have fxy : f x = y := hx.right
          exact ⟨x, Or.inr xA₂, fxy⟩

Note that the expression ``y ∈ image f A₁`` expands to
``∃ x, x ∈ A₁ ∧ f x = y``.
We therefore need to provide three pieces of information: a value of ``x``,
a proof that ``x ∈ A₁``, and a proof that ``f x = y``.
Note also that ``f '' A`` is notation for ``image f A``.

..
   On the eighth line of this proof, after ``Or.inl``,
   we could justify the necessary information by writing
   ``Exists.intro x (and.intro xA₁ fxy)`` in parentheses. But in this case Lean's "anonymous constructor" notation, that is, the corner brackets entered with ``\<`` and ``\>``, allow us to use the more compact expression ``⟨x, xA₁, fxy⟩``.

Exercises
---------

#. Fill in the ``sorry``'s in the last three proofs below.

   .. code-block:: lean

       import Mathlib.Tactic.Basic
       import Mathlib.Algebra.Ring.Divisibility.Lemmas
       open Function Int

       def f (x : ℤ) : ℤ := x + 3
       def g (x : ℤ) : ℤ := -x
       def h (x : ℤ) : ℤ := 2 * x + 3

       example : Injective f :=
       fun x1 x2 ↦
       fun h1 : x1 + 3 = x2 + 3 ↦   -- Lean knows this is the same as f x1 = f x2
       show x1 = x2 from add_right_cancel h1

       example : Surjective f :=
         fun y ↦
         have h1 : f (y - 3) = y :=
           calc
             f (y - 3) = (y - 3) + 3 := by rfl
                     _ = y           := by rw [sub_add_cancel]
       show ∃ x, f x = y from Exists.intro (y - 3) h1

       example (x y : ℤ) (h : 2 * x = 2 * y) : x = y :=
       have h1 : 2 ≠ (0 : ℤ) := by decide  -- this tells Lean to figure it out itself
       show x = y from mul_left_cancel₀ h1 h

       example (x : ℤ) : -(-x) = x := neg_neg x

       example (A B : Type) (u : A → B) (v : B → A) (h : LeftInverse u v) :
         ∀ x, u (v x) = x :=
       h

       example (A B : Type) (u : A → B) (v : B → A) (h : LeftInverse u v) :
         RightInverse v u :=
       h

       -- fill in the sorry's in the following proofs

       example : Injective h :=
       sorry

       example : Surjective g :=
       sorry

       example (A B : Type) (u : A → B) (v1 : B → A) (v2 : B → A)
         (h1 : LeftInverse v1 u) (h2 : RightInverse v2 u) : v1 = v2 :=
       funext
         (fun x ↦
           calc
             v1 x = v1 (u (v2 x)) := by sorry
                _ = v2 x          := by sorry)

#. Fill in the ``sorry`` in the proof below.

   .. code-block:: lean

      import Mathlib.Data.Set.Function
      open Set Function

      variable {X Y : Type}
      variable (A₁ A₂ : Set X)
      variable (f : X → Y)

      theorem image_union : f '' (A₁ ∪ A₂) = f '' A₁ ∪ f '' A₂ := by
        ext y
        constructor
        . intro (h : y ∈ image f (A₁ ∪ A₂))
          cases h with
          | intro x hx =>
            have xA₁A₂ : x ∈ A₁ ∪ A₂ := hx.left
            have fxy : f x = y := hx.right
            cases xA₁A₂ with
            | inl xA₁ => exact Or.inl ⟨x, xA₁, fxy⟩
            | inr xA₂ => exact Or.inr ⟨x, xA₂, fxy⟩
        . intro (h : y ∈ image f A₁ ∪ image f A₂)
          cases h with
          | inl yifA₁ =>
            cases yifA₁ with
            | intro x hx =>
              have xA₁ : x ∈ A₁ := hx.left
              have fxy : f x = y := hx.right
              exact ⟨x, Or.inl xA₁, fxy⟩
          | inr yifA₂ => cases yifA₂ with
            | intro x hx =>
              have xA₂ : x ∈ A₂ := hx.left
              have fxy : f x = y := hx.right
              exact ⟨x, Or.inr xA₂, fxy⟩

      -- remember, x ∈ A ∩ B is the same as x ∈ A ∧ x ∈ B
      example (x : X) (h1 : x ∈ A₁) (h2 : x ∈ A₂) : x ∈ A₁ ∩ A₂ :=
      And.intro h1 h2

      example (x : X) (h1 : x ∈ A₁ ∩ A₂) : x ∈ A₁ :=
      And.left h1

      -- Fill in the proof below.

      example : f '' (A₁ ∩ A₂) ⊆ f '' A₁ ∩ f '' A₂ := by
      intro y
      intro (h1 : y ∈ f '' (A₁ ∩ A₂))
      show y ∈ f '' A₁ ∩ f '' A₂
      sorry
