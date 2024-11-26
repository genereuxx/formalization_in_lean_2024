import FormalizationInLean2024.Defs.FiL_Semantics_Defs

open LoVe

/- # Homework: Semantics

The exercises from this sheet are taken from *Concrete Semantics* by Nipkow and Klein.
The formalisation of the prerequisites in Lean are taken from Blanchette's
*Hitchhicker's guide to logical verification*.
-/

/-
## Exercise 7.1.
Define a function `assigned : Stmt → Set String` that computes the set of variables
that are assigned to in a command. Prove that if some variable is
not assigned to in a command, then that variable is never
modified by the command: `(S,s) ⟹ t → x ∉ FiL.assigned S → s x = t x`.
-/

/-
Exercise 7.2.
Define a recursive function `skip : Stmt → Prop` that determines
if a command behaves like SKIP. Prove `skip c → c ~ SKIP`.
-/

/-
Exercise 7.3.
Define a recursive function `deskip : Stmt → Stmt` that eliminates as many SKIPs as possible from a statement. For example:
`deskip (Stmt.skip; Stmt.whileDo b (Stmt.assign x a; Stmt.skip)) = Stmt.whileDo b (Stmt.assign x a)`
Prove `deskip S ~ S` by induction on `S`. The following lemma might be useful to prove in preparation:
`lemma l7_5 (hSS : S ~ S') : Stmt.whileDo B S ~ Stmt.whileDo B S'`
-/

def deskip : Stmt → Stmt := sorry


/- The following expression should reduce to:
  `Stmt.whileDo b (Stmt.assign x a); Stmt.whileDo b Stmt.skip`-/
#reduce fun b x a => deskip (Stmt.skip; Stmt.whileDo b (Stmt.assign x a ; Stmt.skip);
  Stmt.whileDo b (Stmt.skip ; Stmt.skip))

example (S) : deskip S ~ S := by
  sorry


/-
Exercise 7.4. Define a small-step semantics for the evaluation of arithmetic
expressions:-/

inductive AStep : AExp × State → AExp → Prop where
| eval (x s) : AStep (AExp.var x , s) (AExp.num (s x))
| plus (i j s) : AStep (AExp.add (AExp.num i) (AExp.num j), s) (AExp.num (i + j))
-- First rule for *Plus*
-- Second rule for *Plus*
/-
Complete the definition with two rules for *Plus* that model a left-to-right
evaluation strategy: reduce the first argument with if possible, reduce the
second argument with if the first argument is a number.
Prove that each step preserves the value of the expression:
-/

example : AStep (a, s) a' → eval s a = eval s a' := by
  sorry

/-
Exercise 7.5. Prove or disprove (by giving a counterexample):
• `If b₁ ∧ b₂ then S₁ else S₂ ~ If b₁ then (If b₂ then S₁ else S₂) else S₂`
• `While b₁ ∧ b₁ Do S ∼ While b₁ Do While b₂ Do S`
• `While b₂ ∨ b₂ Do S ∼ While b₁ ∨ b₂ Do S; While b₁ Do S` -/

/-
Exercise 7.6. Define a new loop construct `doWhile S B` (where `S` is
executed once before `B` is tested) in terms of the existing constructs.
Define a recursive translation
`dewhile : Stmt → Stmt`
that replaces all `whileDo B S` by suitable statements that use
`doWhile S B` instead. Prove that your translation preserves the semantics:
`dewhile S ~ S`.
-/

/-
Exercise 7.7. (Small-Step Semantics) Let `x : ℕ → Stmt` be an infinite sequence
of statements and `y : ℕ → State` an infinite sequence of states such that
`x 0 = S; T` and `∀ n. (x n, y n) → (x (n + 1), y (n + 1))`. Prove that
either all `x n` are of the form `Sₙ ; T` and it is always `Sₙ` that is reduced,
or `Sₙ` eventually becomes `Stmt.skip`:
-/
