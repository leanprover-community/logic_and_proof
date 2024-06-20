.. _the_natural_numbers_and_induction_in_lean:

The Natural Numbers and Induction in Lean
=========================================

Induction and Recursion in Lean
-------------------------------

Internally, in Lean, the natural numbers are defined as a type generated inductively from an axiomatically declared ``zero`` and ``succ`` operation:

.. code-block:: lean

    namespace hidden

    open Nat

    -- BEGIN
    inductive Nat : Type
    | zero : Nat
    | succ : Nat → Nat
    -- END
    end hidden

If you click the button that copies this text into the editor in the online version of this textbook, you will see that we wrap it with the phrases ``namespace hidden`` and ``end hidden``. This puts the definition into a new "namespace," so that the identifiers that are defined are ``hidden.Nat``, ``hidden.Nat.zero`` and ``hidden.Nat.succ``, to avoid conflicting with the one that is in the Lean library. Below, we will do that in a number of places where our examples duplicate objects defined in the library. The unicode symbol ``ℕ``, entered with ``\N`` or ``\nat``, is a synonym for ``Nat``.

Declaring ``Nat`` as an inductively defined type means that we can define functions by recursion, and prove theorems by induction. For example, these are the first two recursive definitions presented in the last chapter:

.. code-block:: lean

    import Mathlib.Data.Nat.Defs

    open Nat

    def two_pow : ℕ → ℕ
    | 0        => 1
    | (succ n) => 2 * two_pow n

    def fact : ℕ → ℕ
    | 0        => 1
    | (succ n) => (succ n) * fact n

Addition and numerals are defined in such a way that Lean recognizes ``succ n`` and ``n + 1`` as essentially the same, so we could instead write these definitions as follows:

.. code-block:: lean

    import Mathlib.Data.Nat.Defs

    open Nat

    -- BEGIN
    def two_pow : ℕ → ℕ
    | 0       => 1
    | (n + 1) => 2 * two_pow n

    def fact : ℕ → ℕ
    | 0       => 1
    | (n + 1) => (n + 1) * fact n
    -- END

If we wanted to define the function ``m^n``, we would do that by fixing ``m``, and writing doing the recursion on the second argument:

.. code-block:: lean

    import Mathlib.Data.Nat.Defs

    open Nat

    -- BEGIN
    def pow (m : ℕ) : ℕ → ℕ
    | 0        => 1
    | (n + 1)  => (pow m n) * m
    -- END

In fact, this is how the power function on the natural numbers,
``Nat.pow``, is defined in Lean's library.

Lean is also smart enough to interpret more complicated forms of recursion, like this one:

.. code-block:: lean

    import Mathlib.Data.Nat.Defs

    open Nat

    -- BEGIN
    def fib : ℕ → ℕ
    | 0        => 0
    | 1        => 1
    | (n + 2)  => fib (n + 1) + fib n

In addition to defining functions by recursion, we can prove theorems by induction. In Lean, each clause of a recursive definition results in a new identity. For example, the two clauses in the definition of ``pow`` above give rise to the following two theorems:

.. code-block:: lean

    import Mathlib.Data.Nat.Defs

    open Nat

    -- BEGIN
    example (n : ℕ) : Nat.pow n 0 = 1 := rfl
    example (m n : ℕ) : Nat.pow m (n+1) = (Nat.pow m n) * m := rfl
    -- END

Lean defines the usual notation for exponentiation:

.. code-block:: lean

    import Mathlib.Data.Nat.Defs

    open Nat

    -- BEGIN
    example (n : ℕ) : n^0 = 1 := rfl
    example (m n : ℕ) : m^(n+1) = m^n * m := rfl

    #check @Nat.pow_zero
    #check @Nat.pow_succ
    -- END

Notice that we could alternatively have used ``m * Nat.pow m n``
in the second clause of the definition of ``Nat.pow``.
Of course, we can prove that the two definitions are equivalent using the
commutativity of multiplication, but,
using a proof by induction,
we can also prove it using only the associativity of multiplication,
and the properties ``1 * m = m`` and ``m * 1 = m``.
This is useful, because the power function is also often used in situations
where multiplication is not commutative,
such as with matrix multiplication.
The theorem can be proved in Lean as follows:

.. code-block:: lean

    import Mathlib.Data.Nat.Defs

    open Nat

    -- BEGIN
    example (m n : ℕ) : m^(succ n) = m * m^n := by
      induction n with
      | zero =>
        show m^(succ 0) = m * m^0
        calc
            m^(succ 0) = m^0 * m := by rw [Nat.pow_succ]
                     _ = 1 * m   := by rw [Nat.pow_zero]
                     _ = m       := by rw [Nat.one_mul]
                     _ = m * 1   := by rw [Nat.mul_one]
                     _ = m * m^0 := by rw [Nat.pow_zero]
      | succ n ih =>
        show m^(succ (succ n)) = m * m^(succ n)
        calc
          m^(succ (succ n)) = m^(succ n) * m   := by rw [Nat.pow_succ]
                          _ = (m * m^n) * m    := by rw [ih]
                          _ = m * (m^n * m)    := by rw [Nat.mul_assoc]
                          _ = m * m^(succ n)    := by rw [Nat.pow_succ]
    -- END

This is a typical proof by induction in Lean.
It begins with the tactic ``induction n with``,
which is like ``cases n with``,
but also supplies the induction hypothesis ``ih``
in the successor case.
Here is a shorter proof:

.. code-block:: lean

    import Mathlib.Data.Nat.Defs

    open Nat

    -- BEGIN
    example (m n : ℕ) : m^(succ n) = m * m^n := by
      induction n with
      | zero =>
        show m^(succ 0) = m * m^0
        rw [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_one]
      | succ n ih =>
        show m^(succ (succ n)) = m * m^(succ n)
        rw [Nat.pow_succ, Nat.pow_succ, ← Nat.mul_assoc, ← ih, Nat.pow_succ]
    -- END

Remember that you can write a ``rewrite`` proof incrementally, checking the error messages to make sure things are working so far, and to see how far Lean got.

As another example of a proof by induction, here is a proof of the identity ``m^(n + k) = m^n * m^k``.

.. code-block:: lean

    import Mathlib.Data.Nat.Defs

    open Nat

    -- BEGIN
    example (m n k : ℕ) : m^(n + k) = m^n * m^k := by
      induction n with
      | zero =>
        show m^(0 + k) = m^0 * m^k
        calc m^(0 + k) = m^k       := by rw [Nat.zero_add]
                     _ = 1 * m^k   := by rw [Nat.one_mul]
                     _ = m^0 * m^k := by rw [Nat.pow_zero]
      | succ n ih =>
        show m^(succ n + k) = m^(succ n) * m^k
        calc
          m^(succ n + k) = m^(succ (n + k)) := by rw [Nat.succ_add]
                      _ = m * m^(n + k)    := by rw [Nat.pow_succ']
                      _ = m * (m^n * m^k)    := by rw [ih]
                      _ = (m * m^n) * m^k  := by rw [Nat.mul_assoc]
                      _ = m^(succ n) * m^k := by rw [Nat.pow_succ']
    -- END

Notice the same pattern.
We do induction on ``n``,
and the base case and inductive step are routine.
The theorem is called ``pow_add`` in the library,
and once again, with a bit of cleverness,
we can shorten the proof with ``rewrite``:

.. code-block:: lean

    import Mathlib.Data.Nat.Defs

    open Nat

    -- BEGIN
    example (m n k : ℕ) : m^(n + k) = m^n * m^k := by
      induction n with
      | zero =>
        show m^(0 + k) = m^0 * m^k
        rw [Nat.zero_add, Nat.pow_zero, Nat.one_mul]
      | succ n ih =>
        show m^(succ n + k) = m^(succ n) * m^k
        rw [Nat.succ_add, Nat.pow_succ', ih, ← Nat.mul_assoc, Nat.pow_succ']
    -- END

You should not hesitate to use ``calc``,
however, to make the proofs more explicit.
Remember that you can also use ``calc`` and ``rewrite`` together,
using ``calc`` to structure the calculational proof,
and using ``rewrite`` to fill in each justification step.

Defining the Arithmetic Operations in Lean
------------------------------------------

In fact, addition and multiplication are defined in Lean essentially as described in :numref:`defining_arithmetic_operations`. The defining equations for addition hold by reflexivity, but they are also named ``add_zero`` and ``add_succ``:

.. code-block:: lean

    import Mathlib.Data.Nat.Defs

    open Nat

    variable (m n : ℕ)

    -- BEGIN
    example : m + 0 = m := Nat.add_zero m
    example : m + succ n = succ (m + n) := Nat.add_succ m n
    -- END

Similarly, we have the defining equations for the predecessor function
and multiplication:

.. code-block:: lean

    import Mathlib.Data.Nat.Defs

    -- BEGIN
    #check @Nat.pred_zero
    #check @Nat.pred_succ
    #check @Nat.mul_zero
    #check @Nat.mul_succ
    -- END

Here are the five propositions proved in :numref:`defining_arithmetic_operations`.

.. code-block:: lean

    import Mathlib.Data.Nat.Defs

    open Nat

    namespace hidden

    -- BEGIN
    theorem succ_pred (n : ℕ) : n ≠ 0 → succ (pred n) = n := by
      intro (hn : n ≠ 0)
      cases n with
      | zero => exact absurd rfl (hn : 0 ≠ 0)
      | succ n => rw [Nat.pred_succ]
    -- END
    end hidden

Note that we don't need to use ``induction`` here, only ``cases``.
We prove the next one in term mode instead:

.. code-block:: lean

    import Mathlib.Data.Nat.Defs

    open Nat

    namespace hidden

    -- BEGIN
    theorem zero_add (n : Nat) : 0 + n = n :=
      match n with
      | zero => show 0 + 0 = 0 from rfl
      | succ n =>
        show 0 + succ n = succ n from calc
          0 + succ n = succ (0 + n) := by rfl
                   _ = succ n := by rw [zero_add n]
    -- END

    end hidden

The ``match`` notation is very similar to ``induction``,
except it does not let us provide a name like ``ih``
for the induction hypothesis.
Instead, we call ``zero_add n : 0 + n = n``,
which is the induction hypothesis.
Note that calling ``zero_add (succ n)`` in the same place would be circular,
and if we did so Lean would throw an error.

.. code-block:: lean

    import Mathlib.Data.Nat.Defs

    open Nat

    namespace hidden

    -- BEGIN
    theorem succ_add (m n : Nat) : succ m + n = succ (m + n) :=
      match n with
      | 0 => show succ m + 0 = succ (m + 0) from rfl
      | n + 1 =>
        show succ m + succ n = succ (m + succ n) from calc
             succ m + succ n = succ (succ m + n) := by rfl
                           _ = succ (succ (m + n)) := by rw [succ_add m n]
                           _ = succ (m + succ n) := by rfl
    -- END

    end hidden

Note that this time we used ``0`` and ``n + 1`` in the ``match`` cases.
Here are the final two:

.. code-block:: lean

    import Mathlib.Data.Nat.Defs

    open Nat

    namespace hidden

    -- BEGIN
    theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
      match k with
      | 0 => show m + n + 0 = m + (n + 0) from by
        rw [Nat.add_zero, Nat.add_zero]
      | k + 1 => show m + n + succ k = m + (n + (succ k)) from by
        rw [add_succ, add_assoc m n k, add_succ, add_succ]

    theorem add_comm (m n : Nat) : m + n = n + m :=
      match n with
      | 0 => show m + 0 = 0 + m from by rw [Nat.add_zero, Nat.zero_add]
      | n + 1 => show m + succ n = succ n + m from calc
          m + succ n = succ (m + n) := by rw [add_succ]
                   _ = succ (n + m) := by rw [add_comm m n]
                   _ = succ n + m   := by rw [succ_add]
    -- END

    end hidden



Exercises
---------

#. Formalize as many of the identities from
   :numref:`defining_arithmetic_operations`
   as you can by replacing each `sorry` with a proof.

   .. code-block:: lean

        import Mathlib.Data.Nat.Defs

        open Nat

        --1.a.
        example : ∀ m n k : Nat, m * (n + k) = m * n + m * k := sorry

        --1.b.
        example : ∀ n : Nat, 0 * n = 0 := sorry

        --1.c.
        example : ∀ n : Nat, 1 * n = n := sorry

        --1.d.
        example : ∀ m n k : Nat, (m * n) * k = m * (n * k) := sorry

        --1.e.
        example : ∀ m n : Nat, m * n= n * m := sorry

#. Formalize as many of the identities from :numref:`arithmetic_on_the_natural_numbers` as you can by replacing each `sorry` with a proof.

   .. code-block:: lean

        import Mathlib.Data.Nat.Defs

        open Nat

        --2.a.
        example : ∀ m n k : Nat, n ≤ m → n + k ≤ m  + k := sorry

        --2.b.
        example : ∀ m n k : Nat, n + k ≤ m + k → n ≤ m := sorry

        --2.c.
        example : ∀ m n k : Nat, n ≤ m → n * k ≤ m * k := sorry

        --2.d.
        example : ∀ m n : Nat, m ≥ n → m = n ∨ m ≥ n+1 := sorry

        --2.e.
        example : ∀ n : Nat, 0 ≤ n := sorry
