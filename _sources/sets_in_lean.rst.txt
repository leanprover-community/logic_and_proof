Sets in Lean
============

In the last chapter, we noted that although in axiomatic set theory one considers sets of disparate objects, it is more common in mathematics to consider subsets of some fixed domain, :math:`\mathcal U`. This is the way sets are handled in Lean. For any data type ``U``, Lean gives us a new data type, ``Set U``, consisting of the sets of elements of ``U``. Thus, for example, we can reason about sets of natural numbers, or sets of integers, or sets of pairs of natural numbers.

.. _sets_in_lean_basics:

Basics
------

Given ``A : Set U`` and ``x : U``, we can write ``x ∈ A`` to state that ``x`` is a member of the set ``A``. The character ``∈`` can be typed using ``\in``.

.. code-block:: lean

    import Mathlib.Data.Set.Basic
    open Set

    variable {U : Type}
    variable (A B C : Set U)
    variable (x : U)

    #check x ∈ A
    #check A ∪ B
    #check B \ C
    #check C ∩ A
    #check Cᶜ
    #check ∅ ⊆ A
    #check B ⊆ univ

You can type the symbols ``⊆``, ``∅``, ``∪``, ``∩``, ``\`` as ``\subeq``
``\empty``, ``\un``, ``\i``, and ``\\``, respectively.
We have made the type variable ``U`` implicit,
because it can typically be inferred from context.
The universal set is denoted ``univ``,
and set complementation is denoted with the superscripted letter "c,"
which you can enter as ``\^c`` or ``\compl``.
Basic set-theoretic notions like these are defined in Lean's core library,
but additional theorems and notation are available in an auxiliary library that
we have loaded with the command ``import Mathlib.Data.Set.Basic``,
which has to appear at the beginning of a file.
The command ``open Set`` lets us refer to a theorem named
``Set.mem_union`` as ``mem_union``.

The following patterns can be used to show that ``A`` is a subset of ``B``:

.. code-block:: lean

    import Mathlib.Data.Set.Basic
    open Set

    variable {U : Type}
    variable (A B C : Set U)

    -- BEGIN
    -- term mode
    example : A ⊆ B :=
    fun x ↦
    fun (h : x ∈ A) ↦
    show x ∈ B from sorry

    -- tactic mode
    example : A ⊆ B := by
    intro x
    intro (h : x ∈ A)
    show x ∈ B
    sorry
    -- END

The slogan is ``A ⊆ B`` is the same as ``∀ x, x ∈ A → x ∈ B``.
For Lean this is true *by definition*,
which is why the terms and tactics above are very familiar.

The following patterns can be used to show that ``A`` and ``B`` are equal:

.. code-block:: lean

    import Mathlib.Data.Set.Basic
    open Set

    variable {U : Type}
    variable (A B C : Set U)

    -- BEGIN
    -- term mode
    example : A = B :=
    eq_of_subset_of_subset
      (fun x ↦
        fun (h : x ∈ A) ↦
        show x ∈ B from sorry)
      (fun x ↦
        fun (h : x ∈ B) ↦
        show x ∈ A from sorry)
    -- END

The slogan is ``A = B`` is the same as ``A ⊆ B ∧ B ⊆ A`` is the same
as ``∀ x, x ∈ A ↔ x ∈ B``.
Hence, we can use the following alternatives:

.. code-block:: lean

    import Mathlib.Data.Set.Basic
    open Set

    variable {U : Type}
    variable (A B C : Set U)

    -- BEGIN
    -- term mode
    example : A = B :=
    ext (fun x ↦ Iff.intro
      (fun h : x ∈ A ↦
        show x ∈ B from sorry)
      (fun h : x ∈ B ↦
        show x ∈ A from sorry))

    -- tactic mode
    example : A = B := by
      ext x
      show x ∈ A ↔ x ∈ B
      apply Iff.intro
      . show x ∈ A → x ∈ B
        intro (h : x ∈ A)
        show x ∈ B
        sorry
      . show x ∈ B → x ∈ A
        intro (h : x ∈ B)
        show x ∈ A
        sorry

    -- END

Here, ``ext`` is short for "extensionality."
In term mode, ``Set.ext`` is the following fact:

.. math::

    \forall x \; (x \in A \leftrightarrow x \in B) \to A = B.

This reduces proving :math:`A = B` to proving :math:`\forall x \; (x \in A \leftrightarrow x \in B)`, which we can do using :math:`\forall` and :math:`\leftrightarrow` introduction.
Then, the tactic ``ext`` is the instruction to apply ``Set.ext`` if possible.
We write ``ext x`` to specify the variable name we want to use.

Lean supports the following nifty feature: the defining rules for union,
intersection and other operations on sets are considered to hold "definitionally."
This means that the expressions ``x ∈ A ∩ B`` and ``x ∈ A ∧ x ∈ B``
mean the same thing to Lean.
This is the same for the other constructions on sets;
for example ``x ∈ A \ B`` and ``x ∈ A ∧ ¬ (x ∈ B)``
mean the same thing to Lean.
You can also write ``x ∉ B`` for ``¬ (x ∈ B)``,
where ``∉`` is written using ``\notin``.
The following example illustrates these features.

.. code-block:: lean

    import Mathlib.Data.Set.Basic
    open Set

    variable {U : Type}
    variable (A B C : Set U)

    -- BEGIN
    example : ∀ x, x ∈ A → x ∈ B → x ∈ A ∩ B :=
    fun x ↦
    fun _ : x ∈ A ↦
    fun _ : x ∈ B ↦
    show x ∈ A ∩ B from And.intro ‹x ∈ A› ‹x ∈ B›

    example : A ⊆ A ∪ B :=
    fun x ↦
    fun _ : x ∈ A ↦
    show x ∈ A ∪ B from Or.inl ‹x ∈ A›

    example : ∅ ⊆ A  :=
    fun x ↦
    fun _ : x ∈ ∅ ↦
    show x ∈ A from False.elim ‹x ∈ (∅ : Set U)›
    -- END

Remember from :numref:`definitions_and_theorems` that we can use ``assume``
without a label, and refer back to hypotheses using French quotes,
entered with ``\f<`` and ``\f>``.
We have used this feature in the previous example.
Without that feature, we could have written the examples above as follows:

.. code-block:: lean

    import Mathlib.Data.Set.Basic
    open Set

    variable {U : Type}
    variable (A B C : Set U)

    -- BEGIN
    example : ∀ x, x ∈ A → x ∈ B → x ∈ A ∩ B :=
    fun x ↦
    fun hA : x ∈ A ↦
    fun hB : x ∈ B ↦
    show x ∈ A ∩ B from And.intro hA hB

    example : A ⊆ A ∪ B :=
    fun x ↦
    fun h : x ∈ A ↦
    show x ∈ A ∪ B from Or.inl h

    example : ∅ ⊆ A  :=
    fun x ↦
    fun h : x ∈ ∅ ↦
    show x ∈ A from False.elim h
    -- END

From now on,
we will begin to use ``fun`` and ``have`` command without labels,
but you should feel free to adopt whatever style you prefer.

Notice also that in the last example,
we had to annotate the empty set by writing ``(∅ : Set U)``
to tell Lean which empty set we mean.
Lean can often infer information like this from the context
(for example, from the fact that we are trying to show ``x ∈ A``,
where ``A`` has type ``Set U``), but in this case, it needs a bit more help.

Alternatively, we can use theorems in the Lean library that are designed specifically for use with sets:

.. code-block:: lean

    import Mathlib.Data.Set.Basic
    open Set

    variable {U : Type}
    variable (A B C : Set U)

    -- BEGIN
    example : ∀ x, x ∈ A → x ∈ B → x ∈ A ∩ B :=
    fun x ↦
    fun _ : x ∈ A ↦
    fun _ : x ∈ B ↦
    show x ∈ A ∩ B from mem_inter ‹x ∈ A› ‹x ∈ B›

    example : A ⊆ A ∪ B :=
    fun x ↦
    fun h : x ∈ A ↦
    show x ∈ A ∪ B from mem_union_left B h

    example : ∅ ⊆ A  :=
    fun x ↦
    fun h : x ∈ ∅ ↦
    show x ∈ A from absurd h (not_mem_empty x)
    -- END

Remember that ``absurd`` can be used to prove any fact from two contradictory hypotheses ``h1 : P`` and ``h2 : ¬ P``. Here the ``not_mem_empty x`` is the fact ``x ∉ ∅``. You can see the statements of the theorems using the ``#check`` command in Lean:

.. code-block:: lean

    import Mathlib.Data.Set.Basic
    open Set

    -- BEGIN
    #check @mem_inter
    #check @mem_of_mem_inter_left
    #check @mem_of_mem_inter_right
    #check @mem_union_left
    #check @mem_union_right
    #check @mem_or_mem_of_mem_union
    #check @not_mem_empty
    -- END

Here, the ``@`` symbol in Lean prevents it from trying to fill in implicit arguments automatically, forcing it to display the full statement of the theorem.

The fact that Lean can identify sets with their logical definitions makes it easy to prove inclusions between sets:

.. code-block:: lean

    import Mathlib.Data.Set.Basic
    open Set

    variable {U : Type}
    variable (A B C : Set U)

    -- BEGIN
    example : A \ B ⊆ A :=
    fun x ↦
    fun h : x ∈ A \ B ↦
    show x ∈ A from And.left h

    example : A \ B ⊆ Bᶜ :=
    fun x ↦
    fun h : x ∈ A \ B ↦
    have : x ∉ B := And.right h
    show x ∈ Bᶜ from this
    -- END

Once again, we can use the theorems designed specifically for sets:

.. code-block:: lean

    import Mathlib.Data.Set.Basic
    open Set

    variable {U : Type}
    variable (A B C : Set U)

    -- BEGIN
    example : A \ B ⊆ A :=
    fun x ↦
    fun h : x ∈ A \ B ↦
    show x ∈ A from mem_of_mem_diff h

    example : A \ B ⊆ Bᶜ :=
    fun x ↦
    fun h : x ∈ A \ B ↦
    have : x ∉ B := not_mem_of_mem_diff h
    show x ∈ Bᶜ from this
    -- END

.. this example does not hold in lean4
   The fact that Lean has to unfold definitions means that it can be confused at times. For example, in the proof below, if you replace the last line by ``sorry``, Lean has trouble figuring out that you want it to unfold the subset symbol:

   .. code-block:: lean

        import Mathlib.Data.Set.Basic
        open Set

        variable  {U : Type}
        variable (A B : Set U)

        example : A ∩ B ⊆ B ∩ A :=
        fun x ↦
        fun h : x ∈ A ∩ B ↦
        have h1 : x ∈ A := And.left h
        have h2 : x ∈ B := And.right h
        And.intro h2 h1

   One workaround is to use the ``show`` command; in general, providing Lean with such additional information is often helpful. Another workaround is to give the theorem a name, which prompts Lean to use a slightly different method of processing the proof, fixing the problem as a lucky side effect.

..
   .. code-block:: lean

       variable  {U : Type}
       variables A B : set U

       -- BEGIN
       example : A ∩ B ⊆ B ∩ A :=
       assume x,
       assume h : x ∈ A ∩ B,
       have h1 : x ∈ A, from and.left h,
       have h2 : x ∈ B, from and.right h,
       show x ∈ B ∩ A, from sorry

       theorem my_example : A ∩ B ⊆ B ∩ A :=
       assume x,
       assume h : x ∈ A ∩ B,
       have h1 : x ∈ A, from and.left h,
       have h2 : x ∈ B, from and.right h,
       sorry
       -- END

Some Identities
---------------

Here is the proof of the first identity that we proved informally in the previous chapter:

.. code-block:: lean

    import Mathlib.Data.Set.Basic
    open Set

    variable {U : Type}
    variable (A B C : Set U)

    -- BEGIN
    example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
      ext x
      apply Iff.intro
      . intro (hx : x ∈ A ∩ (B ∪ C))
        have hA: x ∈ A := hx.left
        have hBC: x ∈ B ∪ C := hx.right
        cases hBC with
        | inl hB =>
          have : x ∈ A ∩ B := ⟨hA, hB⟩
          show x ∈ (A ∩ B) ∪ (A ∩ C)
          apply Or.inl
          assumption
        | inr hC =>
          have : x ∈ A ∩ C := ⟨hA, hC⟩
          show x ∈ (A ∩ B) ∪ (A ∩ C)
          apply Or.inr
          assumption
      . intro (hx : x ∈ (A ∩ B) ∪ (A ∩ C))
        cases hx with
        | inl h =>
          show x ∈ A ∩ (B ∪ C)
          apply And.intro
          . show x ∈ A
            exact h.left
          . show x ∈ B ∪ C
            apply Or.inl
            show x ∈ B
            exact h.right
        | inr h =>
          show x ∈ A ∩ (B ∪ C)
          apply And.intro
          . show x ∈ A
            exact h.left
          . show x ∈ B ∪ C
            apply Or.inr
            show x ∈ C
            exact h.right
    -- END

Notice that it is considerably longer than the
informal proof in the last chapter,
because we have spelled out every last detail.
Unfortunately, this does not necessarily make it more readable.
Keep in mind that you can always write long proofs incrementally,
using ``sorry``.
You can also break up long proofs into smaller pieces:

.. code-block:: lean

    import Mathlib.Data.Set.Basic
    open Set

    variable {U : Type}
    variable (A B C : Set U)

    -- BEGIN
    theorem inter_union_subset {x} :
        (x ∈ A ∩ (B ∪ C)) → (x ∈ (A ∩ B) ∪ (A ∩ C)) := by
      intro (hx : x ∈ A ∩ (B ∪ C))
      have hA: x ∈ A := hx.left
      have hBC: x ∈ B ∪ C := hx.right
      cases hBC with
      | inl hB =>
        have : x ∈ A ∩ B := ⟨hA, hB⟩
        show x ∈ (A ∩ B) ∪ (A ∩ C)
        apply Or.inl
        assumption
      | inr hC =>
        have : x ∈ A ∩ C := ⟨hA, hC⟩
        show x ∈ (A ∩ B) ∪ (A ∩ C)
        apply Or.inr
        assumption

    theorem inter_union_inter_subset {x} :
        (x ∈ (A ∩ B) ∪ (A ∩ C)) → (x ∈ A ∩ (B ∪ C)) := by
      intro (hx : x ∈ (A ∩ B) ∪ (A ∩ C))
      cases hx with
      | inl h =>
        show x ∈ A ∩ (B ∪ C)
        apply And.intro
        . show x ∈ A
          exact h.left
        . show x ∈ B ∪ C
          apply Or.inl
          show x ∈ B
          exact h.right
      | inr h =>
        show x ∈ A ∩ (B ∪ C)
        apply And.intro
        . show x ∈ A
          exact h.left
        . show x ∈ B ∪ C
          apply Or.inr
          show x ∈ C
          exact h.right

    example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
      ext x
      constructor
      . exact inter_union_subset A B C
      . exact inter_union_inter_subset A B C
    -- END

Notice that the two theorems depend on the variables ``A``, ``B``, and ``C``, which have to be supplied as arguments when they are applied. They also depend on the underlying type, ``U``, but because the variable ``U`` was marked implicit, Lean figures it out from the context.

Notice also that instead of using ``apply Iff.intro`` to convert the goal
``x ∈ A ∩ (B ∪ C) ↔ x ∈ A ∩ B ∪ A ∩ C`` into
proving each direction,
we can simply use the tactic ``constructor``.
The tactic ``constructor`` also works for splitting up the goal ``A ∧ B``
and the goal ``∃ x, P x``.

.. code-block:: lean

        section
        variable (A B : Prop)

        example : A ∧ B := by
        constructor
        . show A
            sorry
        . show B
            sorry
        end


        section
        variable {U : Type}
        variable (P : U → Prop)
        variable (a : U)

        example : ∃ x, P x := by
        constructor
        . show P a
            sorry
        end

In the last chapter, we showed :math:`(A \cap \overline B) \cup B = B`.
Here is the corresponding proof in Lean:

.. code-block:: lean

    import Mathlib.Data.Set.Basic
    open Set

    variable {U : Type}
    variable (A B C : Set U)

    -- BEGIN
    example : (A ∩ Bᶜ) ∪ B = A ∪ B :=
    calc
      (A ∩ Bᶜ) ∪ B = (A ∪ B) ∩ (Bᶜ ∪ B) := by rw [inter_union_distrib_right]
                 _ = (A ∪ B) ∩ univ     := by rw [compl_union_self]
                 _ = A ∪ B              := by rw [inter_univ]
    -- END

Translated to propositions, the theorem above states that for every pair of elements :math:`A` and :math:`B` in a Boolean algebra, :math:`(A \wedge \neg B) \vee B = B`.

..
   Lean allows us to do calculations on propositions as though they are elements of a Boolean algebra, with equality replaced by ``↔``.

.. TODO(Jeremy): put ``not_or_self`` into the library
.. TODO(Jeremy): give lists of the calculation lemmas for sets and propositions (and make sure the library has a good list)

..
   .. code-block:: lean

       import Mathlib.Logic.Basic

       theorem not_or_self (P : Prop) : (¬ P ∨ P) ↔ True :=
       Iff.intro (λ h ↦ trivial) (λ h ↦ Or.symm (em P))

       -- BEGIN
       variable (A B : Prop)

       example : (A ∧ ¬ B) ∨ B ↔ A ∨ B :=
       calc
         (A ∧ ¬ B) ∨ B ↔ (A ∨ B) ∧ (¬ B ∨ B) := by rw [and_or_right]
                     _ ↔ (A ∨ B) ∧ True      := by rw [not_or_self]
                     _ ↔ (A ∨ B)             := by rw [and_true]
       -- END


Indexed Families
----------------

Remember that if :math:`(A_i)_{i \in I}`
is a family of sets indexed by :math:`I`,
then :math:`\bigcap_{i \in I} A_i` denotes the intersection of all the sets :math:`A_i`, and :math:`\bigcup_{i \in I} A_i` denotes their union.
In Lean, we can specify that ``A`` is a family of sets by writing
``A : I → Set U`` where ``I`` is a ``Type``.
In other words, a family of sets is really a function which for each element
``i`` of type ``I`` returns a set ``A i``.
We can then define the union and intersection as follows:

.. code-block:: lean

    import Mathlib.Data.Set.Basic

    variable {I U : Type}

    def iUnion (A : I → Set U) : Set U := { x | ∃ i : I, x ∈ A i }

    def iInter (A : I → Set U) : Set U := { x | ∀ i : I, x ∈ A i }

    section
    variable (x : U) (A : I → Set U)

    example (h : x ∈ iUnion A) : ∃ i, x ∈ A i := h
    example (h : x ∈ iInter A) : ∀ i, x ∈ A i := h
    end

The examples show that Lean can unfold the definitions so that ``x ∈ iInter A`` can be treated as ``∀ i, x ∈ A i`` and ``x ∈ iUnion A`` can be treated as ``∃ i, x ∈ A i``. To refresh your memory as to how to work with the universal and existential quantifiers in Lean, see :numref:`Chapters %s <first_order_logic_in_lean>`. We can then define notation for the indexed union and intersection:

.. code-block:: lean

    import Mathlib.Data.Set.Basic

    variable {I U : Type}

    def iUnion (A : I → Set U) : Set U := { x | ∃ i : I, x ∈ A i }
    def iInter (A : I → Set U) : Set U := { x | ∀ i : I, x ∈ A i }

    -- BEGIN

    notation3 "⋃ "(...)", "r:60:(scoped f => iUnion f) => r

    notation3 "⋂ "(...)", "r:60:(scoped f => iInter f) => r

    variable (A : I → Set U) (x : U)

    example (h : x ∈ ⋃ i, A i) : ∃ i, x ∈ A i := h
    example (h : x ∈ ⋂ i, A i) : ∀ i, x ∈ A i := h
    -- END

You can type ``⋂`` and ``⋃`` with ``\I`` and ``\Un``, respectively. As with quantifiers, the notation ``⋃ i, A i`` and ``⋂ i, A i`` bind the variable ``i`` in the expression, and the scope extends as widely as possible. For example, if you write ``⋂ i, A i ∪ B``, Lean assumes that the ith element of the sequence is ``A i ∪ B``. If you want to restrict the scope more narrowly, use parentheses.

The good news is that Lean's library does define indexed union and intersection, with this notation, and the definitions are made available with ``import Mathlib.Order.SetNotation``.
The bad news is that it uses a different definition, so that ``x ∈ iInter A`` and ``x ∈ iUnion A`` are *not* definitionally equal to ``∀ i, x ∈ A i`` and ``∃ i, x ∈ A i``, as above.
The good news is that Lean at least knows that they are equivalent,
by two lemmas called ``mem_iUnion`` and ``mem_iInter``.

.. code-block:: lean

    import Mathlib.Order.SetNotation
    open Set

    variable {I U : Type}
    variable {A B : I → Set U}

    #check mem_iUnion
    #check mem_iInter

    theorem exists_of_mem_Union {x : U} (h : x ∈ ⋃ i, A i) :
        ∃ i, x ∈ A i := by
      rw [← mem_iUnion]
      assumption

    theorem mem_Union_of_exists {x : U} (h : ∃ i, x ∈ A i) :
        x ∈ ⋃ i, A i := by
      rw [mem_iUnion]
      assumption

    theorem forall_of_mem_Inter {x : U} (h : x ∈ ⋂ i, A i) :
        ∀ i, x ∈ A i := by
      rw [← mem_iInter]
      assumption

    theorem mem_Inter_of_forall {x : U} (h : ∀ i, x ∈ A i) :
        x ∈ ⋂ i, A i := by
      rw [mem_iInter]
      assumption

The lemma ``mem_iUnion`` says that for any ``x`` we have
``x ∈ ⋃ i, s i ↔ ∃ i, x ∈ s i``.
Being a biconditional,
we can use ``rewrite`` to substitute instances of each side of the other.

Here is an example of how these can be used:

.. code-block:: lean

    import Mathlib.Order.SetNotation
    open Set

    section
    variable {I U : Type}
    variable {A B : I → Set U}


    -- BEGIN
    example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) := by
      ext x
      show x ∈ ⋂ i, A i ∩ B i ↔ x ∈ (⋂ i, A i) ∧ x ∈ ⋂ i, B i
      rw [mem_iInter, mem_iInter, mem_iInter]
      show (∀ (i : I), x ∈ A i ∧ x ∈ B i) ↔
        (∀ (i : I), x ∈ A i) ∧ (∀ (i : I), x ∈ B i)
      constructor
      . intro (h : ∀ (i : I), x ∈ A i ∧ x ∈ B i)
        show (∀ (i : I), x ∈ A i) ∧ ∀ (i : I), x ∈ B i
        constructor
        . show ∀ i, x ∈ A i
          exact fun j ↦ And.left $ h j
        . show ∀ i, x ∈ B i
          exact fun j ↦ And.right $ h j
      . intro (h : (∀ (i : I), x ∈ A i) ∧ ∀ (i : I), x ∈ B i)
        show ∀ i, x ∈ A i ∧ x ∈ B i
        exact fun j ↦ ⟨h.left j, h.right j⟩
    -- END

    end

We first applied extensionality.
Then we force Lean to interpret ``x ∈ (⋂ i, A i) ∩ (⋂ i, B i)``
as the definitionally equal ``x ∈ (⋂ i, A i) ∧ x ∈ ⋂ i, B i``
by writing the latter after ``show``.
Then we used repeated ``rewrite`` tactics to reduce what it means
to be a member of an indexed intersection.
Then we again force Lean to interpret ``x ∈ A i ∩ B i`` as
``x ∈ A i ∧ x ∈ B i`` using show.
Finally, we prove the biconditional,
which is now entirely in terms of first order logic.

.. TODO(Jeremy): we can add this later
    example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
    by finish [set_eq_def]

.. TODO(Jeremy): add all these to the library

Even better,
we can prove introduction and elimination rules for intersection and union:

.. code-block:: lean

    import Mathlib.Order.SetNotation
    open Set

    variable {I U : Type}
    variable {A : I → Set U}

    theorem Inter.intro {x : U} (h : ∀ i, x ∈ A i) : x ∈ ⋂ i, A i := by
      rw [mem_iInter]
      show ∀ i, x ∈ A i
      assumption

    theorem Inter.elim {x : U} (h : x ∈ ⋂ i, A i) (i : I) : x ∈ A i := by
      rw [mem_iInter] at h
      apply h

    theorem Union.intro {x : U} (i : I) (h : x ∈ A i) : x ∈ ⋃ i, A i := by
      rw [mem_iUnion]
      show ∃ i, x ∈ A i
      exact ⟨i, h⟩

    theorem Union.elim {b : Prop} {x : U}
    (h₁ : x ∈ ⋃ i, A i) (h₂ : ∀ (i : I), x ∈ A i → b) : b := by
      rw [mem_iUnion] at h₁
      cases h₁ with
      | intro i hi => exact h₂ i hi

Note that here we did ``rw [mem_iInter] at h`` instructs Lean
to do the substitution along the biconditional proven by ``mem_iInter`` at
the hypothesis ``h``.
If you look at the type of ``h`` before and after this tactic
you will notice the change.

We could not use ``rewrite``,
and just the introduction and elimination rules:

.. code-block:: lean

    import Mathlib.Order.SetNotation
    open Set

    variable {I U : Type}
    variable {A : I → Set U}

    theorem Inter.intro {x : U} (h : ∀ i, x ∈ A i) : x ∈ ⋂ i, A i := by
      rw [mem_iInter]
      show ∀ i, x ∈ A i
      assumption

    theorem Inter.elim {x : U} (h : x ∈ ⋂ i, A i) (i : I) : x ∈ A i := by
      rw [mem_iInter] at h
      apply h

    theorem Union.intro {x : U} (i : I) (h : x ∈ A i) : x ∈ ⋃ i, A i := by
      rw [mem_iUnion]
      show ∃ i, x ∈ A i
      exact ⟨i, h⟩

    theorem Union.elim {b : Prop} {x : U}
    (h₁ : x ∈ ⋃ i, A i) (h₂ : ∀ (i : I), x ∈ A i → b) : b := by
      rw [mem_iUnion] at h₁
      cases h₁ with
      | intro i hi => exact h₂ i hi

    -- BEGIN
    example (x : U) : x ∈ ⋂ i, A i :=
    Inter.intro $
    fun i ↦
    show x ∈ A i from sorry

    example (x : U) (i : I) (h : x ∈ ⋂ i, A i) : x ∈ A i :=
    Inter.elim h i

    example (x : U) (i : I) (h : x ∈ A i) : x ∈ ⋃ i, A i :=
    Union.intro i h

    example (C : Prop) (x : U) (h : x ∈ ⋃ i, A i) : C :=
    Union.elim h $
    fun i ↦
    fun h : x ∈ A i ↦
    show C from sorry
    -- END

Remember that the dollar sign saves us the trouble of having to put parentheses around the rest of the proof. Notice that with ``Inter.intro`` and ``Inter.elim``, proofs using indexed intersections looks just like proofs using the universal quantifier. Similarly, ``Union.intro`` and ``Union.elim`` mirror the introduction and elimination rules for the existential quantifier.
The following example provides one direction of an equivalence proved above,
just using the introduction and elimination rules:

.. code-block:: lean

    import Mathlib.Order.SetNotation
    open Set

    variable {I U : Type}
    variable {A : I → Set U}

    theorem Inter.intro {x : U} (h : ∀ i, x ∈ A i) : x ∈ ⋂ i, A i := by
      rw [mem_iInter]
      show ∀ i, x ∈ A i
      assumption

    theorem Inter.elim {x : U} (h : x ∈ ⋂ i, A i) (i : I) : x ∈ A i := by
      rw [mem_iInter] at h
      apply h

    theorem Union.intro {x : U} (i : I) (h : x ∈ A i) : x ∈ ⋃ i, A i := by
      rw [mem_iUnion]
      show ∃ i, x ∈ A i
      exact ⟨i, h⟩

    theorem Union.elim {b : Prop} {x : U}
    (h₁ : x ∈ ⋃ i, A i) (h₂ : ∀ (i : I), x ∈ A i → b) : b := by
      rw [mem_iUnion] at h₁
      cases h₁ with
      | intro i hi => exact h₂ i hi

    section
    -- BEGIN
    variable {I U : Type}
    variable (A : I → Set U) (B : I → Set U) (C : Set U)

    example : (⋂ i, A i ∩ B i) ⊆ (⋂ i, A i) ∩ (⋂ i, B i) :=
    fun x : U ↦
    fun h : x ∈ ⋂ i, A i ∩ B i ↦
    have h1 : x ∈ ⋂ i, A i :=
      Inter.intro $
      fun i : I ↦
      have h2 : x ∈ A i ∩ B i := Inter.elim h i
      show x ∈ A i from And.left h2
    have h2 : x ∈ ⋂ i, B i :=
        Inter.intro $
        fun i : I ↦
        have h2 : x ∈ A i ∩ B i := Inter.elim h i
        show x ∈ B i from And.right h2
    show x ∈ (⋂ i, A i) ∩ (⋂ i, B i) from And.intro h1 h2
    -- END
    end

You are asked to prove the other direction in the exercises below.
Here is an example that shows how to use the introduction and elimination rules for indexed union:

.. code-block:: lean

    import Mathlib.Order.SetNotation
    open Set

    variable {I U : Type}
    variable {A : I → Set U}

    theorem Inter.intro {x : U} (h : ∀ i, x ∈ A i) : x ∈ ⋂ i, A i := by
      rw [mem_iInter]
      show ∀ i, x ∈ A i
      assumption

    theorem Inter.elim {x : U} (h : x ∈ ⋂ i, A i) (i : I) : x ∈ A i := by
      rw [mem_iInter] at h
      apply h

    theorem Union.intro {x : U} (i : I) (h : x ∈ A i) : x ∈ ⋃ i, A i := by
      rw [mem_iUnion]
      show ∃ i, x ∈ A i
      exact ⟨i, h⟩

    theorem Union.elim {b : Prop} {x : U}
    (h₁ : x ∈ ⋃ i, A i) (h₂ : ∀ (i : I), x ∈ A i → b) : b := by
      rw [mem_iUnion] at h₁
      cases h₁ with
      | intro i hi => exact h₂ i hi

    section
    -- BEGIN
    variable {I U : Type}
    variable (A : I → Set U) (B : I → Set U) (C : Set U)

    example : (⋃ i, C ∩ A i) ⊆ C ∩ (⋃i, A i) :=
    fun x : U ↦
    fun h : x ∈ ⋃ i, C ∩ A i ↦
    Union.elim h $
    fun i ↦
    fun h1 : x ∈ C ∩ A i ↦
    have h2 : x ∈ C := And.left h1
    have h3 : x ∈ A i := And.right h1
    have h4 : x ∈ ⋃ i, A i := Union.intro i h3
    show x ∈ C ∩ ⋃ i, A i from And.intro h2 h4
    -- END
    end

Once again, we ask you to prove the other direction in the exercises below.

Sometimes we want to work with families :math:`(A_{i, j})_{i \in I, j \in J}`
indexed by two variables.
This is also easy to manage in Lean: if we declare ``A : I → J → Set U``,
then given ``i : I`` and ``j : J``,
we have that ``A i j : Set U``.
(You should interpret the expression ``I → J → Set U`` as
``I → (J → Set U)``,
so that ``A i`` has type ``J → Set U``,
and then ``A i j`` has type ``Set U``.)
Here is an example of a proof involving a such a doubly-indexed family:

.. code-block:: lean

    import Mathlib.Order.SetNotation
    open Set

    variable {I U : Type}
    variable {A : I → Set U}

    theorem Inter.intro {x : U} (h : ∀ i, x ∈ A i) : x ∈ ⋂ i, A i := by
      rw [mem_iInter]
      show ∀ i, x ∈ A i
      assumption

    theorem Inter.elim {x : U} (h : x ∈ ⋂ i, A i) (i : I) : x ∈ A i := by
      rw [mem_iInter] at h
      apply h

    theorem Union.intro {x : U} (i : I) (h : x ∈ A i) : x ∈ ⋃ i, A i := by
      rw [mem_iUnion]
      show ∃ i, x ∈ A i
      exact ⟨i, h⟩

    theorem Union.elim {b : Prop} {x : U}
    (h₁ : x ∈ ⋃ i, A i) (h₂ : ∀ (i : I), x ∈ A i → b) : b := by
      rw [mem_iUnion] at h₁
      cases h₁ with
      | intro i hi => exact h₂ i hi

    -- BEGIN
    section
    variable {I U : Type}
    variable (A : I → J → Set U)

    example : (⋃i, ⋂j, A i j) ⊆ (⋂j, ⋃i, A i j) :=
    fun x : U ↦
    fun h : x ∈ ⋃i, ⋂j, A i j ↦
    Union.elim h $
    fun i ↦
    fun h1 : x ∈ ⋂ j, A i j ↦
    show x ∈ ⋂j, ⋃i, A i j from
        Inter.intro $
        fun j ↦
        have h2 : x ∈ A i j := Inter.elim h1 j
        Union.intro i h2
    end
    -- END

Power Sets
----------

We can also define the power set in Lean:

.. code-block:: lean

    variable {U : Type}

    def powerset (A : Set U) : Set (Set U) := {B : Set U | B ⊆ A}

    example (A B : Set U) (h : B ∈ powerset A) : B ⊆ A :=
    h

As the example shows,
``B ∈ powerset A`` is then definitionally the same as ``B ⊆ A``.

In fact, ``powerset`` is defined in Lean in exactly this way,
and is available to you when you ``import Mathlib.Data.Set.Basic``
and ``open Set``.
Here is an example of how it is used:

.. code-block:: lean

    import Mathlib.Data.Set.Basic
    open Set

    variable  {U : Type}
    variable (A B : Set U)

    -- BEGIN
    #check powerset A

    example : A ∈ powerset (A ∪ B) :=
    fun x ↦
    fun _ : x ∈ A ↦
    show x ∈ A ∪ B from Or.inl ‹x ∈ A›
    -- END

In essence, the example proves ``A ⊆ A ∪ B``.
In the exercises below, we ask you to prove,
formally, that for every ``A B : Set U``,
we have ``powerset A ⊆ powerset B``

Exercises
---------

#. Fill in the ``sorry``'s.

   .. code-block:: lean

        import Mathlib.Data.Set.Basic
        open Set

        variable  {U : Type}
        variable (A B C : Set U)

        -- BEGIN
        example : ∀ x, x ∈ A ∩ C → x ∈ A ∪ B :=
        sorry

        example : ∀ x, x ∈ (A ∪ B)ᶜ → x ∈ Aᶜ :=
        sorry
        -- END

#. Fill in the ``sorry``.

   .. code-block:: lean

    import Mathlib.Data.Set.Basic
    open Set

    section
    variable {U : Type}

    /- defining "disjoint" -/

    def disj (A B : Set U) : Prop := ∀ ⦃x⦄, x ∈ A → x ∈ B → False

    example (A B : Set U) (h : ∀ x, ¬ (x ∈ A ∧ x ∈ B)) :
      disj A B :=
    fun x ↦
    fun h1 : x ∈ A ↦
    fun h2 : x ∈ B ↦
    have h3 : x ∈ A ∧ x ∈ B := And.intro h1 h2
    show False from h x h3

    -- notice that we do not have to mention x when applying
    --   h : disj A B
    example (A B : Set U) (h1 : disj A B) (x : U)
        (h2 : x ∈ A) (h3 : x ∈ B) :
      False :=
    h1 h2 h3

    -- the same is true of ⊆
    example (A B : Set U) (x : U) (h : A ⊆ B) (h1 : x ∈ A) :
      x ∈ B :=
    h h1

    example (A B C D : Set U) (h1 : disj A B) (h2 : C ⊆ A)
        (h3 : D ⊆ B) :
      disj C D :=
    sorry
    end

#. Prove the following facts about indexed unions and intersections, using the theorems ``Inter.intro``, ``Inter.elim``, ``Union.intro``, and ``Union.elim`` listed above.

   .. code-block:: lean

        import Mathlib.Data.Set.Basic
        import Mathlib.Order.SetNotation
        open Set

        section
        variable {I U : Type}
        variable {A B : I → Set U}

        theorem Inter.intro {x : U} (h : ∀ i, x ∈ A i) : x ∈ ⋂ i, A i := by
        rw [mem_iInter]
        show ∀ i, x ∈ A i
        assumption

        theorem Inter.elim {x : U} (h : x ∈ ⋂ i, A i) (i : I) : x ∈ A i := by
        rw [mem_iInter] at h
        apply h

        theorem Union.intro {x : U} (i : I) (h : x ∈ A i) : x ∈ ⋃ i, A i := by
        rw [mem_iUnion]
        show ∃ i, x ∈ A i
        exact ⟨i, h⟩

        theorem Union.elim {b : Prop} {x : U}
        (h₁ : x ∈ ⋃ i, A i) (h₂ : ∀ (i : I), x ∈ A i → b) : b := by
        rw [mem_iUnion] at h₁
        cases h₁ with
        | intro i hi => exact h₂ i hi

        end

        -- BEGIN
        variable {I U : Type}
        variable (A : I → Set U) (B : I → Set U) (C : Set U)

        example : (⋂ i, A i) ∩ (⋂ i, B i) ⊆ (⋂ i, A i ∩ B i) :=
        sorry

        example : C ∩ (⋃i, A i) ⊆ ⋃i, C ∩ A i :=
        sorry
        -- END

#. Prove the following fact about power sets.
   You can use the theorems ``Subset.trans`` and ``Subset.refl``.

    .. code-block:: lean

        import Mathlib.Data.Set.Basic
        open Set

        -- BEGIN
        variable {U : Type}
        variable (A B C : Set U)

        -- For this exercise these two facts are useful
        example (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C :=
        Subset.trans h1 h2

        example : A ⊆ A :=
        Subset.refl A

        example (h : A ⊆ B) : powerset A ⊆ powerset B :=
        sorry

        example (h : powerset A ⊆ powerset B) : A ⊆ B :=
        sorry
        -- END
