Propositional Logic in Lean
===========================

In this chapter, you will learn how to write proofs in Lean. We will start with a purely mechanical translation that will enable you to represent any natural deduction proof in Lean. We will see, however, that such a style of writing proofs is not very intuitive, nor does it yield very readable proofs. It also does not scale well.

We will then consider some mechanisms that Lean offers that support a more forward-directed style of argumentation. Since these proofs look more like informal proofs but can be directly translated to natural deduction, they will help us understand the relationship between the two.

Expressions for Propositions and Proofs
---------------------------------------

At its core, Lean is what is known as a *type checker*. This means that we can write expressions and ask the system to check that they are well formed, and also ask the system to tell us what type of object they denote. Try this:

.. code-block:: lean

    section
    -- BEGIN
    variable (A B C : Prop)

    #check A ∧ ¬ B → C
    -- END
    end

In the online version of this text, you can press the "try it!" button to copy the example to an editor window, and then hover over the markers on the text to read the messages.

In the example, we declare three variables ranging over propositions, and ask Lean to check the expression ``A ∧ ¬ B → C``. The output of the ``#check`` command is ``A ∧ ¬ B → C : Prop``, which asserts that ``A ∧ ¬ B → C`` is of type ``Prop``. In Lean, every well-formed expression has a type.

The logical connectives are rendered in unicode. The following chart shows you how you can type these symbols in the editor, and also provides ascii equivalents, for the purists among you.

+-----------+-------------------+---------------------------------+
| Unicode   | Ascii             | Lean input                      |
+-----------+-------------------+---------------------------------+
|           | true              |                                 |
+-----------+-------------------+---------------------------------+
|           | false             |                                 |
+-----------+-------------------+---------------------------------+
| ¬         | not               | ``\not``, ``\neg``              |
+-----------+-------------------+---------------------------------+
| ∧         | /\\               | ``\and``                        |
+-----------+-------------------+---------------------------------+
| ∨         | \\/               | ``\or``                         |
+-----------+-------------------+---------------------------------+
| →         | ->                | ``\to``, ``\r``, ``\imp``       |
+-----------+-------------------+---------------------------------+
| ↔         | <->               | ``\iff``, ``\lr``               |
+-----------+-------------------+---------------------------------+
| ∀         | forall            | ``\all``                        |
+-----------+-------------------+---------------------------------+
| ∃         | exists            | ``\ex``                         |
+-----------+-------------------+---------------------------------+
| λ         | fun               | ``\lam``, ``\fun``              |
+-----------+-------------------+---------------------------------+
| ≠         | ~=                | ``\ne``                         |
+-----------+-------------------+---------------------------------+

So far, we have only talked about the first seven items on the list. We will discuss the quantifiers, lambda, and equality later. Try typing some expressions and checking them on your own. You should try changing one of the variables in the example above to ``D``, or inserting a nonsense symbol into the expression, and take a look at the error message that Lean returns.

In addition to declaring variables, if ``P`` is any expression of type ``Prop``, we can declare the hypothesis that ``P`` is true:

.. code-block:: lean

    section
    variable (A B : Prop)
    -- BEGIN
    variable (h : A ∧ ¬ B)

    #check h
    -- END
    end

Formally, what is going on is that any proposition can be viewed as a type, namely, the type of proofs of that proposition. A hypothesis, or premise, is just a variable of that type. Building proofs is then a matter of writing down expressions of the correct type. For example, if ``h`` is any expression of type ``A ∧ B``, then ``And.left h`` is an expression of type ``A``, and ``And.right h`` is an expression of type ``B``. In other words, if ``h`` is a proof of ``A ∧ B``, and ``And.left h`` is a name for the proof you get by applying the left elimination rule for and:

.. raw:: html

   <img src="_static/propositional_logic_in_lean.1.png">

.. raw:: latex

   \begin{center}
   \AXM{\vdots}
   \noLine
   \UIM{P}
   \noLine
   \UIM{\vdots}
   \noLine
   \UIM{A \wedge B}
   \UIM{A}
   \DP
   \end{center}

Similarly, ``And.right h`` is the proof of ``B`` you get by applying the right elimination rule. So, continuing the example above, we can write

.. code-block:: lean

    section
    variable (A B : Prop)
    -- BEGIN
    variable (h : A ∧ ¬ B)

    #check And.left h
    #check And.right h
    -- END
    end

The two expressions represent, respectively, these two proofs:

.. raw:: html

   <img src="_static/propositional_logic_in_lean.2.png">

.. raw:: latex

   \begin{center}
   \AXM{}
   \RLM{h}
   \UIM{A \wedge \neg B}
   \UIM{A}
   \DP
   \quad\quad
   \AXM{}
   \RLM{h}
   \UIM{A \wedge \neg B}
   \UIM{\neg B}
   \DP
   \end{center}

Notice that in this way of representing natural deduction proofs, there are no "free floating" hypotheses. Every hypothesis has a label. In Lean, we will typically use expressions like ``h``, ``h1``, ``h2``, ... to label hypotheses, but you can use any identifier you want.

If ``h1`` is a proof of ``A`` and ``h2`` is a proof of ``B``, then ``And.intro h1 h2`` is a proof of ``A ∧ B``. So we can continue the example above:

.. code-block:: lean

    section
    variable (A B : Prop)
    -- BEGIN
    variable (h : A ∧ ¬ B)

    #check And.intro (And.right h) (And.left h)
    -- END

    end

This corresponds to the following proof:

.. raw:: html

   <img src="_static/propositional_logic_in_lean.2b.png">

.. raw:: latex

   \begin{center}
   \AXM{}
   \RLM{h}
   \UIM{A \wedge \neg B}
   \UIM{\neg B}
   \AXM{}
   \RLM{h}
   \UIM{A \wedge \neg B}
   \UIM{A}
   \BIM{\neg B \wedge A}
   \DP
   \end{center}

What about implication? The elimination rule is easy: if ``h₁`` is a proof of ``A → B`` and ``h₂`` is a proof of ``A`` then ``h₁ h₂`` is a proof of ``B``. Notice that we do not even need to name the rule: you just write ``h₁`` followed by ``h₂``, as though you are applying the first to the second. If ``h₁`` and ``h₂`` are compound expressions, put parentheses around them to make it clear where each one begins and ends.

.. code-block:: lean

    section
    variable (A B C D : Prop)

    -- BEGIN
    variable (h1 : A → (B → C))
    variable (h2 : D → A)
    variable (h3 : D)
    variable (h4 : B)

    #check h2 h3
    #check h1 (h2 h3)
    #check (h1 (h2 h3)) h4
    -- END

    end

Lean adopts the convention that applications associate to the left, so that an expression ``h1 h2 h3`` is interpreted as ``(h1 h2) h3``. Implications associate to the *right*, so that ``A → B → C`` is interpreted as ``A → (B → C)``. This may seem funny, but it is a convenient way to represent implications that take multiple hypotheses, since an expression ``A → B → C → D → E`` means that ``E`` follows from ``A``, ``B``, ``C``, and ``D``. So the example above could be written as follows:

.. code-block:: lean

    section
    variable (A B C D : Prop)

    -- BEGIN
    variable (h1 : A → (B → C))
    variable (h2 : D → A)
    variable (h3 : D)
    variable (h4 : B)

    #check h2 h3
    #check h1 (h2 h3)
    #check h1 (h2 h3) h4
    -- END

    end

Notice that parentheses are still needed in the expression ``h1 (h2 h3)``.

The implication introduction rule is the tricky one,
because it can cancel a hypothesis.
In terms of Lean expressions,
the rule translates as follows.
Suppose ``A`` and ``B`` have type ``Prop``,
and, assuming ``hA`` is the premise that ``A`` holds,
``hB`` is proof of ``B``, possibly involving ``hA``.
Then the expression ``fun h : A ↦ hB`` is a proof of ``A → B``.
You can type ``\mapsto`` for the ``↦`` symbol.
For example, we can construct a proof of ``A → A ∧ A`` as follows:

.. code-block:: lean

    section
    variable (A : Prop)

    -- BEGIN
    #check (fun h : A ↦ And.intro h h)
    -- END

    end

We can read ``fun`` as "assume ``h``".
In fact, ``fun`` stands for "function",
since a proof of ``A → B`` is a function from the type of
proofs of ``A`` to the type of proofs of ``B``.

Notice that we no longer have to declare ``A`` as a premise;
we don't have ``variable (h : A)``.
The expression ``fun h : A ↦ hB``
makes the premise ``h`` local to the expression in parentheses,
and we can refer to ``h`` later within the parentheses.
Given the assumption ``h : A``,
``And.intro h h`` is a proof of ``A ∧ A``,
and so the expression ``fun h : A ↦ And.intro h h``
is a proof of ``A → A ∧ A``.
In this case,
we could leave out the parentheses because the expression is unambiguous:

.. code-block:: lean

    section
    variable (A : Prop)

    -- BEGIN
    #check fun h : A ↦ And.intro h h
    -- END
    end

Above, we proved ``¬ B ∧ A`` from the premise ``A ∧ ¬ B``. We can instead obtain a proof of ``A ∧ ¬ B → ¬ B ∧ A`` as follows:

.. code-block:: lean

    section
    variable (A B : Prop)

    -- BEGIN
    #check (fun h : A ∧ ¬ B ↦ And.intro (And.right h) (And.left h))
    -- END

    end

All we did was move the premise into a local ``fun`` expression.

(By the way, the ``fun`` command is just alternative syntax for the lambda symbol, so we could also have written this:

.. code-block:: lean

    section
    variable (A B : Prop)

    -- BEGIN
    #check (λ h : A ∧ ¬ B ↦ And.intro (And.right h) (And.left h))
    -- END
    end

You will learn more about the lambda symbol later.)

More commands
-------------

Let us introduce a new Lean command, ``example``. This command tells Lean that you are about to prove a theorem, or, more generally, write down an expression of the given type. It should then be followed by the proof or expression itself.

.. code-block:: lean

    section
    variable (A B : Prop)

    -- BEGIN
    example : A ∧ ¬ B → ¬ B ∧ A :=
    fun h : A ∧ ¬ B ↦
    And.intro (And.right h) (And.left h)
    -- END

    end

When given this command,
Lean checks the expression after the ``:=`` and makes sure it has the right type.
If so,
it accepts the expression as a valid proof. If not, it raises an error.

Because the ``example`` command provides information as to the
type of the expression that follows
(in this case, the proposition being proved),
it sometimes enables us to omit other information.
For example, we can leave off the type of the assumption:

.. code-block:: lean

    section
    variable (A B : Prop)

    -- BEGIN
    example : A ∧ ¬ B → ¬ B ∧ A :=
    fun h ↦
    And.intro (And.right h) (And.left h)
    -- END

    end

Because Lean knows we are trying to prove an implication with premise
``A ∧ ¬ B``,
it can infer that when we write ``fun h ↦``, the identifier ``h`` labels the assumption ``A ∧ ¬ B``.

We can also go in the other direction,
and provide the system with *more* information, with the word ``show``.
If ``A`` is a proposition and ``h : A`` is a proof,
the expression "``show A from h``" means the same thing as ``h`` alone,
but it signals the intention that ``h`` is a proof of ``A``.
When Lean checks this expression,
it confirms that ``h`` really is a proof of ``A``,
before parsing the expression surrounding it.
So, in our example,
we could also write:

.. code-block:: lean

    section
    variable (A B : Prop)

    -- BEGIN
    example : A ∧ ¬ B → ¬ B ∧ A :=
    fun h : A ∧ ¬ B ↦
    show ¬ B ∧ A from And.intro (And.right h) (And.left h)
    -- END

    end

We could even annotate the smaller expressions ``And.right h`` and ``And.left h``, as follows:

.. code-block:: lean


    section
    variable (A B : Prop)

    -- BEGIN
    example : A ∧ ¬ B → ¬ B ∧ A :=
    fun h : A ∧ ¬ B ↦
    show ¬ B ∧ A from And.intro
      (show ¬ B from And.right h)
      (show A from And.left h)
    -- END

    end


Although in the examples above the ``show`` commands were not necessary,
there are a number of good reasons to use this style.
First, and perhaps most importantly,
it makes the proofs easier for us humans to read.
Second, it makes the proofs easier to *write*:
if you make a mistake in a proof,
it is easier for Lean to figure out where you went wrong and provide a
meaningful error message if you make your intentions clear.
Finally, proving information in the ``show``
clause often makes it possible for you to omit information in other places,
since Lean can infer that information from your stated intentions.

There are notational variants.
Rather than declare variables and premises beforehand,
you can also present them as "arguments" to the example, followed by a colon:

.. code-block:: lean

    example (A B : Prop) : A ∧ ¬ B → ¬ B ∧ A :=
    fun h : A ∧ ¬ B ↦
    show ¬ B ∧ A from And.intro
      (show ¬ B from And.right h)
      (show A from And.left h)

There are two more tricks that can help you write proofs in Lean.
The first is using ``sorry``,
which is a magical term in Lean which provides a proof of anything at all.
It is also known as "cheating".
But cheating can help you construct legitimate proofs incrementally:
if Lean accepts a proof with ``sorry``'s,
the parts of the proof you have written so far have passed
Lean's checks for correctness.
All you need to do is replace each ``sorry``
with a real proof to complete the task.

.. code-block:: lean

    section
    variable (A B : Prop)

    -- BEGIN
    example : A ∧ ¬ B → ¬ B ∧ A :=
    fun h ↦ sorry

    example : A ∧ ¬ B → ¬ B ∧ A :=
    fun h ↦ And.intro sorry sorry

    example : A ∧ ¬ B → ¬ B ∧ A :=
    fun h ↦ And.intro (And.right h) sorry

    example : A ∧ ¬ B → ¬ B ∧ A :=
    fun h ↦ And.intro (And.right h) (And.left h)
    -- END

    end

The second trick is the use of *placeholders*,
represented by the underscore symbol.
When you write an underscore in an expression,
you are asking the system to try to fill in the value for you.
This falls short of calling full-blown automation to prove a theorem;
rather, you are asking Lean to infer the value from the context.
If you use an underscore where a proof should be,
Lean typically will *not* fill in the proof,
but it will give you an error message that tells you what is missing.
This will help you write proof terms incrementally,
in a backward-driven fashion.
In the example above, try replacing each ``sorry`` by an underscore, ``_``,
and take a look at the resulting error messages.
In each case, the error tells you what needs to be filled in,
and the variables and hypotheses that are available to you at that stage.

One more tip: if you want to delimit the scope of variables or premises introduced with the ``variable`` command, put them in a block that begins with the word ``section`` and ends with the word ``end``.

Building Natural Deduction Proofs
---------------------------------

In this section, we describe a mechanical translation from natural deduction proofs, by giving a translation for each natural deduction rule. We have already seen some of the correspondences, but we repeat them all here, for completeness.

Implication
~~~~~~~~~~~

We have already explained that implication introduction is implemented with ``fun``, and implication elimination is written as application.

.. code-block:: lean

    section
    variable (A B : Prop)

    example : A → B :=
    fun h : A ↦
    show B from sorry

    section
    variable (h1 : A → B) (h2 : A)

    example : B := h1 h2
    end
    end

Note that there is a section within a section to further limit the scope of
two new variables.

Conjunction
~~~~~~~~~~~

We have already seen that and-introduction is implemented with ``And.intro``, and the elimination rules are ``And.left`` and ``And.right``.

.. code-block:: lean

    section
    variable (h1 : A) (h2 : B)

    example : A ∧ B := And.intro h1 h2
    end

    section
    variable (h : A ∧ B)

    example : A := And.left h
    example : B := And.right h
    end

Disjunction
~~~~~~~~~~~

The or-introduction rules are given by ``Or.inl`` and ``Or.inr``.

.. code-block:: lean

    section
    variable (h : A)

    example : A ∨ B := Or.inl h
    end

    section
    variable (h : B)

    example : A ∨ B := Or.inr h
    end

The elimination rule is the tricky one. To prove ``C`` from ``A ∨ B``, you need three arguments: a proof ``h`` of ``A ∨ B``, a proof of ``C`` from ``A``, and a proof of ``C`` from ``B``. Using line breaks and indentation to highlight the structure as a proof by cases, we can write it with the following form:

.. code-block:: lean

    section
    -- BEGIN
    variable (h : A ∨ B) (ha : A → C) (hb : B → C)
    example : C :=
    Or.elim h
      (fun h1 : A ↦
        show C from ha h1)
      (fun h1 : B ↦
        show C from hb h1)
    -- END
    end

Notice that we can reuse the label ``h1`` in each branch, since, conceptually, the two branches are disjoint.

Negation
~~~~~~~~

Internally, negation ``¬ A`` is defined by ``A → False``, which you can think of as saying that ``A`` implies something impossible. The rules for negation are therefore similar to the rules for implication. To prove ``¬ A``, assume ``A`` and derive a contradiction.

.. code-block:: lean

    example : ¬ A :=
    fun h : A ↦
    show False from sorry

If you have proved a negation ``¬ A``, you can get a contradiction by applying it to a proof of ``A``.

.. code-block:: lean

    section
    -- BEGIN
    variable (h1 : ¬ A) (h2 : A)

    example : False := h1 h2
    -- END

    end

Truth and falsity
~~~~~~~~~~~~~~~~~

The *ex falso* rule is called ``False.elim``:

.. code-block:: lean

    section
    -- BEGIN
    variable (h : False)

    example : A := False.elim h
    -- END
    end

There isn't much to say about ``True`` beyond the fact that it is trivially true:

.. code-block:: lean

    example : True := trivial

Bi-implication
~~~~~~~~~~~~~~

The introduction rule for "if and only if" is ``Iff.intro``.

.. code-block:: lean

    example : A ↔ B :=
    Iff.intro
      (fun h : A ↦
        show B from sorry)
      (fun h : B ↦
        show A from sorry)

As usual, we have chosen indentation to make the structure clear. Notice that the same label, ``h``, can be used on both branches, with a different meaning in each, because the scope of ``fun`` is limited to the expression in which it appears.

The elimination rules are ``Iff.mp`` and ``Iff.mpr`` for "modus ponens"
and "modus ponens (reverse)":

.. code-block:: lean

    section
    variable (h1 : A ↔ B)
    variable (h2 : A)

    example : B := Iff.mp h1 h2
    end

    section
    variable (h1 : A ↔ B)
    variable (h2 : B)

    example : A := Iff.mpr h1 h2
    end

Reductio ad absurdum (proof by contradiction)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Finally, there is the rule for proof by contradiction, which we will discuss in greater detail in :numref:`Chapter %s <classical_reasoning>`. It is included for completeness here.

The rule is called ``byContradiction``.
It has one argument, which is a proof of ``False`` from ``¬ A``.
To use the rule, you have to ask Lean to allow classical reasoning,
by writing ``open Classical``.
You can do this at the beginning of the file,
or any time before using it.
If you say ``open Classical`` in a section,
it will remain in scope for that section.

.. code-block:: lean

    section
      open Classical

      example : A :=
      byContradiction
        (fun h : ¬ A ↦
          show False from sorry)
    end

Examples
~~~~~~~~

In the last chapter, we constructed the following proof of :math:`A \to C` from :math:`A \to B` and :math:`B \to C`:

.. raw:: html

   <img src="_static/propositional_logic_in_lean.3.png">

.. raw:: latex

   \begin{center}
   \AXM{}
   \RLM{1}
   \UIM{A}
   \AXM{A \to B}
   \BIM{B}
   \AXM{B \to C}
   \BIM{C}
   \RLM{1}
   \UIM{A \to C}
   \DP
   \end{center}

We can model this in Lean as follows:

.. code-block:: lean

    section
    variable (A B C : Prop)

    -- BEGIN
    variable (h1 : A → B)
    variable (h2 : B → C)

    example : A → C :=
    fun h : A ↦
    show C from h2 (h1 h)
    -- END

    end

Notice that the hypotheses in the natural deduction proof that are not canceled are declared as variables in the Lean version.

We also constructed the following proof:

.. raw:: html

   <img src="_static/propositional_logic_in_lean.4.png">

.. raw:: latex

   \begin{center}
   \AXM{}
   \RLM{2}
   \UIM{A \to (B \to C)}
   \AXM{}
   \RLM{1}
   \UIM{A \wedge B}
   \UIM{A}
   \BIM{B \to C}
   \AXM{}
   \RLM{1}
   \UIM{A \wedge B}
   \UIM{B}
   \BIM{C}
   \RLM{1}
   \UIM{A \wedge B \to C}
   \RLM{2}
   \UIM{(A \to (B \to C)) \to (A \wedge B \to C)}
   \DP
   \end{center}

Here is how it is written in Lean:

.. code-block:: lean

    example (A B C : Prop) : (A → (B → C)) → (A ∧ B → C) :=
      fun h1 : A → (B → C) ↦
      fun h2 : A ∧ B ↦
      show C from h1 (And.left h2) (And.right h2)

This works because ``And.left h2`` is a proof of ``A``, and ``And.right h2`` is a proof of ``B``.

Finally, we constructed the following proof of :math:`A \wedge (B \vee C) \to (A \wedge B) \vee (A \wedge C)`:

.. raw:: html

   <img src="_static/propositional_logic_in_lean.5.png">

.. raw:: latex

   \begin{center}
   \AXM{}
   \RLM{2}
   \UIM{A \wedge (B \vee C)}
   \UIM{B \vee C}
   \AXM{}
   \RLM{2}
   \UIM{A \wedge (B \vee C)}
   \UIM{A}
   \AXM{}
   \RLM{1}
   \UIM{B}
   \BIM{A \wedge B}
   \UIM{(A \wedge B) \vee (A \wedge C)}
   \AXM{}
   \RLM{2}
   \UIM{A \wedge (B \vee C)}
   \UIM{A}
   \AXM{}
   \RLM{1}
   \UIM{C}
   \BIM{A \wedge C}
   \UIM{(A \wedge B) \vee (A \wedge C)}
   \RLM{1}
   \TIM{(A \wedge B) \vee (A \wedge C)}
   \RLM{2}
   \UIM{(A \wedge (B \vee C)) \to ((A \wedge B) \vee
     (A \wedge C))}
   \DP
   \end{center}

Here is a version in Lean:

.. code-block:: lean

    example (A B C : Prop) : A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) :=
    fun h1 : A ∧ (B ∨ C) ↦
    Or.elim (And.right h1)
      (fun h2 : B ↦
        show (A ∧ B) ∨ (A ∧ C) from Or.inl (And.intro (And.left h1) h2))
      (fun h2 : C ↦
        show (A ∧ B) ∨ (A ∧ C)
          from Or.inr (And.intro (And.left h1) h2))

In fact,
bearing in mind that ``fun`` is alternative syntax for the symbol ``λ``,
and that Lean can often infer the type of an assumption,
we can make the proof remarkably brief:

.. code-block:: lean

    example (A B C : Prop) : A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) :=
    λ h1 ↦ Or.elim (And.right h1)
      (λ h2 ↦ Or.inl (And.intro (And.left h1) h2))
      (λ h2 ↦ Or.inr (And.intro (And.left h1) h2))

The proof is cryptic, though.
Using such a style makes proofs hard to write, read, understand, maintain, and debug.
Tactic mode is one way in which we can mitigate some of these issues.

Tactic Mode
-----------

So far we have only explained one mode for writing proofs in Lean,
namely "term mode".
In term mode we can directly write proofs as syntactic expressions.
In this section we introduce "tactic mode",
which allows us to write proofs more interactively,
with tactics as instructions to follow for building such a proof.
The statement to be proved at a given point is called the *goal*,
and instructions make progress by transforming
the goal into something that is easier to prove.
Once the tactic mode proof is complete,
Lean should be able to turn it into a proof term by following the instructions.

Tactics can be very powerful tools,
bearing much of the tedious work and
allowing us to write much shorter proofs.
We will slowly introduce them as we go.

We can enter tactic mode by writing the keyword ``by`` after ``:=``:

.. code-block:: lean

    -- term mode
    example (A B C : Prop) : A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) :=
    fun h1 : A ∧ (B ∨ C) ↦
    Or.elim (And.right h1)
      (fun h2 : B ↦
        show (A ∧ B) ∨ (A ∧ C) from Or.inl (And.intro (And.left h1) h2))
      (fun h2 : C ↦
        show (A ∧ B) ∨ (A ∧ C)
          from Or.inr (And.intro (And.left h1) h2))

    -- tactic mode
    example (A B C : Prop) : A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) := by
      intro (h1 : A ∧ (B ∨ C))
      cases h1 with
      | intro h1 h2 => cases h2 with
        | inl h2 =>
          apply Or.inl
          apply And.intro
          exact h1
          exact h2
        | inr h2 =>
          apply Or.inr
          apply And.intro
          exact h1
          exact h2

Instead of ``fun h1 ↦ h2`` we use ``intro (h1 : A ∧ (B ∨ C))``
to "introduce" the assumption ``h1``,
then give instructions for ``h2``.

Instead of ``Or.elim h`` and ``And.elim h`` we use ``cases h with``
and use ``|`` to list the possible cases in which the proof ``h`` was made,
then continuing the proof in each case.
For conjunction, there is only one possible way in which ``h`` was made,
which is by ``And.intro h1 h2`` (Lean only allows ``intro h1 h2``).
For disjunction there are two cases,
``h`` could be either ``Or.inl h1`` or ``Or.inr h2``
(again we must write ``inl h1`` and ``inr h2``).

Instead of immediately supplying ``Or.inl``, ``Or.inr`` and ``And.intro``
with all its arguments we can (for example) ``apply Or.inl`` and
fill in the missing parts afterwards.
In fact, Lean sees ``Or.inl : A → A ∨ B`` as a proof of a conditional,
and for any ``h : A → B``,
``apply h`` will change the goal from ``B`` to ``A``.
We can see this as "since ``A`` implies ``B``, in order to prove ``B``
it suffices to prove ``A``".
Finally, when our goal is ``A`` and ``h1 : A`` we can close the goal
by writing ``exact A``.

We will mix tactics and terms in order to suit our needs.
We will slowly introduce more and more tactics throughout this textbook.

Note that tactic mode proofs are sensitive to indentation and returns.
On the other hand, term mode proofs are not sensitive to whitespace.
We could write every term mode proof on a single line.
For both modes,
we will adopt conventions for indentation and line breaks that
show the structure of proofs and make them easier to read.


Forward Reasoning
-----------------

Lean supports forward reasoning by allowing you to write
proofs using ``have``,
which is both a term mode expression and a tactic.
Notice that ``show`` is also a tactic.

.. code-block:: lean

    section
    variable (A B C : Prop)

    -- BEGIN
    variable (h1 : A → B)
    variable (h2 : B → C)

    -- term mode
    example : A → C :=
      fun h : A ↦
      have h3 : B := h1 h
      show C from h2 h3

    -- tactic mode
    example : A → C := by
      intro (h : A)
      have h3 : B := h1 h
      show C
      exact h2 h3
    -- END

    end

Writing a proof with
``have h : A := _`` then continuing the proof with
``... h ...`` has the same effect as writing ``... _ ...``.
This ``have`` command checks that ``_`` is a proof of ``A``,
and then give you the label ``h`` to use in place of ``_``.
Thus the last line of the previous proof can be thought of as
abbreviating ``exact h2 (h1 h)``,
since ``h3`` abbreviates ``h1 h``.
Such abbreviations can make a big difference,
especially when the proof ``_`` is long and repeatedly used.

There are a number of advantages to using ``have``.
For one thing, it makes the proof more readable:
the example above states ``B`` explicitly as an auxiliary goal.
It can also save repetition:
``h3`` can be used repeatedly after it is introduced,
without duplicating the proof.
Finally, it makes it easier to construct and debug the proof:
stating ``B`` as an auxiliary goal makes it easier for Lean to deliver an
informative error message when the goal is not properly met.

Note that ``have`` and ``exact`` are mixing term mode and tactic mode,
since the expression ``h1 h`` is a term mode proof of ``B``
and ``h2 h3`` is a term mode proof of ``C``.

Previously we have considered the following statement,
which we partially translate to tactic mode:

.. code-block:: lean

    example (A B C : Prop) : (A → (B → C)) → (A ∧ B → C) :=
      fun h1 : A → (B → C) ↦
      fun h2 : A ∧ B ↦
      show C from h1 (And.left h2) (And.right h2)

    example (A B C : Prop) : (A → (B → C)) → (A ∧ B → C) := by
      intro (h1 : A → (B → C)) (h2 : A ∧ B)
      exact h1 (And.left h2) (And.right h2)

Note that ``intro`` can introduce multiple assumptions at once.
Using ``have``, it can be written more perspicuously as follows:

.. code-block:: lean

    example (A B C : Prop) : (A → (B → C)) → (A ∧ B → C) := by
      intro (h1 : A → (B → C)) (h2 : A ∧ B)
      have h3 : A := And.left h2
      have h4 : B := And.right h2
      exact h1 h3 h4

We can be even more verbose, and add another line:

.. code-block:: lean

    example (A B C : Prop) : (A → (B → C)) → (A ∧ B → C) := by
      intro (h1 : A → (B → C)) (h2 : A ∧ B)
      have h3 : A := And.left h2
      have h4 : B := And.right h2
      have h5 : B → C := h1 h3
      show C
      exact h5 h4

Adding more information doesn't always make a proof more readable; when the individual expressions are small and easy enough to understand, spelling them out in detail can introduce clutter. As you learn to use Lean, you will have to develop your own style, and use your judgment to decide which steps to make explicit.

Here is how some of the basic inferences look, when expanded with ``have``. In the and-introduction rule, it is a matter showing each conjunct first, and then putting them together:

.. code-block:: lean

    example (A B : Prop) : A ∧ B → B ∧ A := by
      intro (h1 : A ∧ B)
      have h2 : A := And.left h1
      have h3 : B := And.right h1
      show B ∧ A
      exact And.intro h3 h2

Compare that with this version, which instead states first that we will use the ``And.intro`` rule, and then makes the two resulting goals explicit:

.. code-block:: lean

    example (A B : Prop) : A ∧ B → B ∧ A := by
      intro (h1 : A ∧ B)
      apply And.intro
      . show B
        exact And.right h1
      . show A
        exact And.left h1

Notice the use of ``.`` to seperate the two remaining goals;
it is sensitive to indentation.

Once again, at issue is only readability.
Lean does just fine with the following short term mode version:

.. code-block:: lean

    example (A B : Prop) : A ∧ B → B ∧ A :=
    λ h ↦ And.intro (And.right h) (And.left h)

When using the or-elimination rule, it is often clearest to state the relevant disjunction explicitly:

.. code-block:: lean

    example (A B C : Prop) : C := by
    have h : A ∨ B := sorry
    show C
    apply Or.elim h
    . intro (hA : A)
      sorry
    . intro (hB : B)
      sorry

Here is a ``have``-structured presentation of an example from the previous section:

.. code-block:: lean

    -- tactic mode
    example (A B C : Prop) : A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) := by
    intro (h1 : A ∧ (B ∨ C))
    have h2 : A := And.left h1
    have h3 : B ∨ C := And.right h1
    show (A ∧ B) ∨ (A ∧ C)
    apply Or.elim h3
    . intro (h4 : B)
      have h5 : A ∧ B := And.intro h2 h4
      show (A ∧ B) ∨ (A ∧ C)
      exact Or.inl h5
    . intro (h4 : C)
      have h5 : A ∧ C := And.intro h2 h4
      show (A ∧ B) ∨ (A ∧ C)
      exact Or.inr h5

    -- term mode
    example (A B C : Prop) : A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) :=
    fun h1 : A ∧ (B ∨ C) ↦
    have h2 : A := And.left h1
    have h3 : B ∨ C := And.right h1
    show (A ∧ B) ∨ (A ∧ C) from
      Or.elim h3
        (fun h4 : B ↦
          have h5 : A ∧ B := And.intro h2 h4
          show (A ∧ B) ∨ (A ∧ C) from Or.inl h5)
        (fun h4 : C ↦
          have h5 : A ∧ C := And.intro h2 h4
          show (A ∧ B) ∨ (A ∧ C) from Or.inr h5)


.. _definitions_and_theorems:

Definitions and Theorems
------------------------

Lean allows us to name definitions and theorems for later use. For example, here is a definition of a new "connective":

.. code-block:: lean

    def triple_and (A B C : Prop) : Prop :=
    A ∧ (B ∧ C)

As with the ``example`` command, it does not matter whether the arguments ``A``, ``B``, and ``C`` are declared beforehand with the ``variable`` command, or with the definition itself. We can then apply the definition to any expressions:

.. code-block:: lean

    def triple_and (A B C : Prop) : Prop :=
    A ∧ (B ∧ C)

    section
    -- BEGIN
    variable (D E F G : Prop)

    #check triple_and (D ∨ E) (¬ F → G) (¬ D)
    -- END
    end

Later, we will see more interesting examples of definitions, like the following function from natural numbers to natural numbers, which doubles its input:

.. code-block:: lean

    import Mathlib.Data.Nat.Defs

    def double (n : ℕ) : ℕ := n + n

What is more interesting right now is that Lean also allows us to name theorems, and use them later, as rules of inference. For example, consider the following theorem:

.. code-block:: lean

    theorem and_commute (A B : Prop) : A ∧ B → B ∧ A :=
    fun h ↦ And.intro (And.right h) (And.left h)

Once we have defined it, we can use it freely:

.. code-block:: lean

    theorem and_commute (A B : Prop) : A ∧ B → B ∧ A :=
    fun h ↦ And.intro (And.right h) (And.left h)

    section
    -- BEGIN
    variable (C D E : Prop)
    variable (h1 : C ∧ ¬ D)
    variable (h2 : ¬ D ∧ C → E)

    example : E := h2 (and_commute C (¬ D) h1)
    --END

    end

It is annoying in this example that we have to give the arguments ``C`` and ``¬ D`` explicitly, because they are implicit in ``h1``. In fact, Lean allows us to tell this to Lean in the definition of ``and_commute``:

.. code-block:: lean

    theorem and_commute {A B : Prop} : A ∧ B → B ∧ A :=
    fun h ↦ And.intro (And.right h) (And.left h)

Here the squiggly braces indicate that the arguments ``A`` and ``B`` are *implicit*, which is to say, Lean should infer them from the context when the theorem is used. We can then write the following instead:

.. code-block:: lean

    theorem and_commute {A B : Prop} : A ∧ B → B ∧ A :=
    fun h ↦ And.intro (And.right h) (And.left h)

    section
    -- BEGIN
    variable (C D E : Prop)
    variable (h1 : C ∧ ¬ D)
    variable (h2 : ¬ D ∧ C → E)

    example : E := h2 (and_commute h1)
    -- END

    end

Indeed, Lean's library has a theorem, ``and_comm``,
defined in exactly this way.

The two definitions yield the same result.

Definitions and theorems are important in mathematics; they allow us to build up complex theories from fundamental principles. Lean also accepts the word ``lemma`` instead of ``theorem``.

What is interesting is that in interactive theorem proving, we can even define familiar patterns of inference. For example, all of the following inferences were mentioned in the last chapter:

.. code-block:: lean

    namespace hidden

    variable {A B : Prop}

    theorem Or_resolve_left (h1 : A ∨ B) (h2 : ¬ A) : B :=
    Or.elim h1
      (fun h3 : A ↦ show B from False.elim (h2 h3))
      (fun h3 : B ↦ show B from h3)

    theorem Or_resolve_right (h1 : A ∨ B) (h2 : ¬ B) : A :=
    Or.elim h1
      (fun h3 : A ↦ show A from h3)
      (fun h3 : B ↦ show A from False.elim (h2 h3))

    theorem absurd (h1 : ¬ A) (h2 : A) : B :=
    False.elim (h1 h2)

    end hidden

In fact, Lean's library defines ``Or.resolve_left``, ``Or.resolve_right``,
and ``absurd``.
We used the ``namespace`` command to avoid naming conflicts,
which would have raised an error.

When we ask you to prove basic facts from propositional logic in Lean, as with propositional logic, our goal is to have you learn how to use Lean's primitives. As a result, for those exercises, you should not use facts from the library. As we move towards real mathematics, however, you can use facts from the library more freely.

Additional Syntax
-----------------

In this section, we describe some extra syntactic features of Lean, for power users. The syntactic gadgets are often convenient, and sometimes make proofs look prettier.

For one thing, you can use subscripted numbers with a backslash. For example, you can write ``h₁`` by typing ``h\1``. The labels are irrelevant to Lean, so the difference is only cosmetic.

Another feature is that you can omit the label in ``fun`` and ``intro``,
providing an "anonymous" assumption.
In tactic mode you can call the anonymous assumption
using the tactic ``assumption``:

.. code-block:: lean

    example : A → A ∨ B := by
      intro
      show A ∨ B
      apply Or.inl
      assumption

In term mode you can call the anonymous assumption
by enclosing the proposition name in French quotes,
given by typing ``\f<`` and ``\f>``.

.. code-block:: lean

    example : A → A ∨ B :=
    fun _ ↦ Or.inl ‹A›

You can also use the word ``have`` without giving a label, and refer back to them using the same conventions. Here is an example that uses these features:

.. code-block:: lean

    theorem my_theorem {A B C : Prop} :
        A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) := by
      intro (h : A ∧ (B ∨ C))
      have : A := And.left h
      have : (B ∨ C) := And.right h
      show (A ∧ B) ∨ (A ∧ C)
      apply Or.elim ‹B ∨ C›
      . intro
        have : A ∧ B := And.intro ‹A› ‹B›
        show (A ∧ B) ∨ (A ∧ C)
        apply Or.inl
        assumption
      . intro
        have : A ∧ C := And.intro ‹A› ‹C›
        show (A ∧ B) ∨ (A ∧ C)
        apply Or.inr
        assumption

Another trick is that you can write ``h.left`` and ``h.right`` instead of
``And.left h`` and ``And.right h`` whenever ``h`` is a conjunction,
and you can write ``⟨h1, h2⟩``
using ``\<`` and ``\>`` (noting the difference with the French quotes)
instead of ``And.intro h1 h2``
whenever Lean can figure out that a conjunction is what you are trying to prove.
With these conventions, you can write the following:

.. code-block:: lean

    example (A B : Prop) : A ∧ B → B ∧ A :=
    fun h : A ∧ B ↦
    show B ∧ A from ⟨h.right, h.left⟩

This is nothing more than shorthand for the following:

.. code-block:: lean

    example (A B : Prop) : A ∧ B → B ∧ A :=
    fun h : A ∧ B ↦
    show B ∧ A from And.intro (And.right h) (And.left h)

Even more concisely, you can write this:

.. code-block:: lean

    example (A B : Prop) : A ∧ B → B ∧ A :=
    fun h ↦ ⟨h.right, h.left⟩

You can even take apart a conjunction with ``fun``, so that this works:

.. code-block:: lean

    example (A B : Prop) : A ∧ B → B ∧ A :=
    fun ⟨h₁, h₂⟩ ↦ ⟨h₂, h₁⟩

Similarly, if ``h`` is a biconditional, you can write ``h.mp`` and ``h.mpr`` instead of ``Iff.mp h`` and ``Iff.mpr h``, and you can write ``⟨h1, h2⟩`` instead of ``Iff.intro h1 h2``. As a result, Lean understands these proofs:

.. code-block:: lean

    example (A B : Prop) : B ∧ (A ↔ B) → A :=
    fun ⟨hB, hAB⟩ ↦
    hAB.mpr hB

    example (A B : Prop) : A ∧ B ↔ B ∧ A :=
    ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₂, h₁⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₂, h₁⟩⟩

Finally, you can add comments to your proofs in two ways. First, any text after a double-dash ``--`` until the end of a line is ignored by the Lean processOr. Second, any text between ``/-`` and ``-/`` denotes a block comment, and is also ignored. You can nest block comments.

.. code-block:: lean

    /- This is a block comment.
       It can fill multiple lines. -/

    example (A : Prop) : A → A :=
    fun a : A ↦      -- assume the antecedent
    show A from a     -- use it to establish the conclusion

Exercises
---------

Prove the following in both term mode and tactic mode:

.. code-block:: lean

    section
    variable (A B C D : Prop)

    -- BEGIN
    example : A ∧ (A → B) → B :=
    sorry

    example : A → ¬ (¬ A ∧ B) :=
    sorry

    example : ¬ (A ∧ B) → (A → ¬ B) :=
    sorry

    example (h₁ : A ∨ B) (h₂ : A → C) (h₃ : B → D) : C ∨ D :=
    sorry

    example (h : ¬ A ∧ ¬ B) : ¬ (A ∨ B) :=
    sorry

    example : ¬ (A ↔ ¬ A) :=
    sorry
    -- END

    end
