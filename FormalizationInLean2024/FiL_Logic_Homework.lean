import Mathlib.Data.Set.Basic

/- # Homework: Logic

Some of the exercises from this sheet are taken from
  - J. Avigad et al., Logic and Proof, online
  - J. Blanchette et al, The Hitchhiker’s Guide to Logical Verification, 2024 LMU Desktop Edition
-/

/-
## Exercise 1
Show the following exercises about propositional logic.
At least two of your solutions should be in term mode.
You should **not** need to use classical logic.
-/

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

theorem not_iff_not_self : ¬ (A ↔ ¬ A) :=
  sorry

/-
## Exercice 2
Show the following exercises about first order logic.
At least two of your solutions should be in term mode.
You should **not** need to use classical logic.
-/

/- Show the barber paradox. -/
section
  variable (Person : Type) (shaves : Person → Person → Prop) (barber : Person)
  variable (h : ∀ x, shaves barber x ↔ ¬ shaves x x)

  example : False := sorry
end

section

variable (U : Type) (A B C : U → Prop)

example : (∀ x, A x ∧ B x) → ∀ x, A x :=
  sorry

example : (∃ x, A x) → ∃ x, A x ∨ B x :=
  sorry

example (h1 : ∀ x, A x → B x) (h2 : ∃ x, A x) : ∃ x, B x :=
  sorry

example (h1 : ∃ x, A x ∧ B x) (h2 : ∀ x, B x → C x) :
    ∃ x, A x ∧ C x :=
  sorry

example : (¬ ∃ x, A x) → ∀ x, ¬ A x :=
  sorry

example : (∀ x, ¬ A x) → ¬ ∃ x, A x :=
  sorry

example : (∀ x, A x → ¬ B x) → ¬ ∃ x, A x ∧ B x :=
  sorry

/- Warning : `simp` closes the goal using classical logic. -/
example : ((¬ ∀ x, A x) → ¬ ∀ x, ¬¬ A x) ↔ ((∀ x, ¬¬ A x) → ¬¬ ∀ x, A x) :=
  sorry

end

/- ## Exercise 3: Intuitionistic Logic

Intuitionistic logic is extended to classical logic by assuming a classical
axiom. There are several possibilities for the choice of axiom. In this
question, we are concerned with the logical equivalence of three different
axioms: -/

def ExcludedMiddle : Prop :=
  ∀a : Prop, a ∨ ¬ a

def Peirce : Prop :=
  ∀a b : Prop, ((a → b) → a) → a

def DoubleNegation : Prop :=
  ∀a : Prop, (¬¬ a) → a

/- For the proofs below, avoid using theorems from Lean's `Classical` namespace.

3.1. Prove the following implication using tactics.

Hint: You will need `Or.elim` and `False.elim`. You can use
`rw [ExcludedMiddle]` to unfold the definition of `ExcludedMiddle`,
and similarly for `Peirce`. -/

theorem Peirce_of_EM :
  ExcludedMiddle → Peirce :=
sorry

/- 3.2. Prove the following implications using tactics. -/

theorem DN_of_Peirce :
  Peirce → DoubleNegation :=
sorry

theorem EM_of_DN :
  DoubleNegation → ExcludedMiddle :=
sorry

/- ## Exercise 4
The drinker paradox, or the drinker theorem, is a theorem in classical predicate logic.
It can be stated as follows:
  There is someone in the pub such that,
  if he or she is drinking,
  then everyone in the pub is drinking.

Formalise this statement in Lean and prove it using classical logic.
You can assume the pub is nonempty.
-/


/- ## Exercise 5
### De Morgan's laws and intuitionistic logic
-/

/-
First, show (the first of) De Morgan's laws.
The following tactics might prove useful:
  `constructor`, `rcases`, `left`, `right`

You can't use `push_neg` and classical reasoning.
-/
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  sorry

/-
Now show it in term mode using only introduction and elimination rules.
-/
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q :=
  sorry

/-
For this law, one direction requires classical reasoning. Show it using only a combination
of `constructor`, `rcases`, `left`, `right` and the theorem `em`. (You can also use `by_cases`).
-/
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  sorry

/-
Using only `em` and intuitionistic logic, show the following again in term mode.
-/
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q :=
  sorry
