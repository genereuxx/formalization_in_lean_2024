import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Nat

/-
## Exercise 1
Use induction to prove the following examples.
-/

example (p q : ℕ) (m : ℕ) : ∃ a b : ℕ, (p + √q) ^ m = a + b * √q := by
  sorry

example (n : ℕ) : ∑ i ∈ Finset.range (n + 1), i ^ 3 = ((n * (n + 1)) ^ 2 / 4) := by
  sorry

/-
## Exercise 2
Use the appropriate induction principle to show the following facts.
-/
section
variable {n : ℕ}

example (h0 : n ≠ 0) : ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  sorry

example (h0 : n ≠ 0) : ∑ i ∈ Finset.range n, (i * i !) = (n !) - 1 := by
  sorry

example (hle : 4 ≤ n) : 2 ^ n ≤ n ! := by
  sorry

example (h0 : n ≠ 0) : 2 ^ (n - 1) ≤ n ! := by
  sorry

example (h0 : n ≠ 0) : n ! ≤ n ^ (n - 1) := by
  sorry

end
/-
## Bonus
Complete these two questions correctly for a bonus point.

### a)

In the last two examples, were the `(h0 : n ≠ 0)` necessary? Why?


### b)
Show the following lemma.

Hint: You might first want to show that
`∀ k ≥ 2, (k + 1) ^ n ≤ k ^ (2 * n)`.
-/
lemma pow_le_fac (k : ℕ) : ∃ N, ∀ n ≥ N, k ^ n ≤ n ! := by
  sorry


/-
## Exercise 3
In Lean, `Finset` represent the type of finite sets.
As it is defined in terms of `List`, which is an inductive type,
we get a panoply of inductive principle.

Use the appropriate induction lemmas to show the following fact.

Hint: Try to look through the different induction principles in the library.
The key ingredient is to figure out what your induction principle should look like.
You might want to use https://leansearch.net/.

-/


open Finset in
example {α : Type*} [LinearOrder α] {s : Finset α} (hs : s.Nonempty) :
    ∃ a ∈ s, ∀ σ ∈ s, σ ≤ a := by
  sorry

/-
## Exercise 4 (*)
Use `Nat.strong_induction_on` to prove the following fact.
If you prefer, you may also do a recursive proof.
-/

example (n : ℕ) (hle : 12 ≤ n) : ∃ a b, n = 4 * a + 5 * b := by
  sorry

/-
## Exercise 5
Use the appropriate induction lemma to show the following.
-/

example {s : Finset α} (f : α → ℕ) (he : ∀ x ∈ s, Even (f x)) :
    Even (∑ x ∈ s, f x) := by
  sorry

/-
## Exercise 6 (*)
In any introduction to number theory, one of the very first result proved
formalises the notion of "dividing with remainder".

Here is a classical presentation on the natural numbers.
Complete the proof of the formalisation.

### Lemma
  If `a` and `b` are integers, with `b ≥ 1`, then there exist unique
  integers `q` and `r`, with `0 ≤ r ≤ b − 1`, such that `a = qb + r`.
  We call `q` the “quotient”, and `r` the “remainder”.

#### Proof by induction.
We begin by proving the existence of `q` and `r`.
For each `b ≥ 1`,we proceed by induction on `a ≥ 0`.
If `a ≤ b−1`, then the result follows with `q = 0` and `r = a`.

Otherwise assume that the result holds for `0,1,2,...,a−1`, where `a ≥ b`.
Then `a − 1 ≥ a − b` so, by the induction hypothesis,
there exist integers `Q` and `r`, with `0 ≤ r ≤ b − 1`, for which `a − b = Qb + r`.
Therefore `a = qb + r` with `q = Q + 1`.
-/


example (a b : ℕ) (hb : 1 ≤ b) : ∃ q r : ℕ, a = q * b + r ∧ 0 ≤ r ∧ r ≤ b - 1 := by
  induction' a using Nat.strong_induction_on with a ih generalizing b
  /-
  Try to follow the structure of the paper proof as much as you can.
  Remember that you can use `linarith` and `omega` in the appropriate cases.
  The only theorem that I used is `Nat.sub_eq_iff_eq_add`.
  -/
  sorry

/-
## Exercise 7 (**)

Finish the above formalisation by proving that the `q` and `r` you obtained
are unique. You can follow this proof.

If `a = qb + r = Qb + R`, then `b` divides `(q − Q)b = R − r`.
However `0 ≤ r`, `R ≤ b − 1` so that `|R − r| ≤ b − 1 `, and `b | R − r`.
However, `b | R − r` implies that `b ≤ R - r` or `R - r = 0`.
Therefore `R − r = 0`, and so `Q − q = 0`.
In other words `q = Q` and `r = R`; that is, the pair `q`,`r` is unique.

You can use `∃!` to represent uniqueness or directly the definition
`∃ (x : α), p x ∧ ∀ (y : α), p y → y = x`.
-/
