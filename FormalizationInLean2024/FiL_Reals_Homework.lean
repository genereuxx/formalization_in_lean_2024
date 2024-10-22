import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/- # Homework: Reals

Some of the exercises from this sheet are taken from
  - K. Buzzard, Formalising Mathematics

Exercises marked with stars (*) (**) are more difficult.
-/

/- ## Exercise 1 -/

/--
Our custom definition of the absolute value on `ℝ`. -/
noncomputable def av (a : ℝ) : ℝ := if 0 ≤ a then a else -a

/- Setting the notation `|·|` to refer to our definition. -/
@[inherit_doc av]
macro:max (priority := 1001) atomic("|" noWs) a:term noWs "|" : term => `(av $a)

/-
Show that our absolute value respects these usual basic properties.

You are not allowed to use the theorem that relates to Mathlib's absolute value `abs`.

You can unfold the `if · then · else ·` with `if_pos` and `if_neg`.
You can also use `split` to case split on the condition.
-/
lemma av_of_nonneg (h : 0 ≤ a) : |a| = a := sorry

lemma av_of_neg (h : a < 0) : |a| = -a := sorry

lemma av_nonneg : 0 ≤ |a| := sorry

lemma av_pos (h : a ≠ 0) : 0 < |a| := sorry

lemma le_av {a : ℝ} : a ≤ |a| ∧ -a ≤ |a| := sorry

lemma av_le_iff {a b : ℝ} : |a| ≤ b ↔ a ≤ b ∧ -a ≤ b := sorry

example {a b ε : ℝ} (h : |a - b| ≤ ε) : a - ε ≤ b ∧ b ≤ a + ε := sorry

example {a b ε : ℝ} (h : |a - b| ≤ ε) : b - ε ≤ a ∧ a ≤ b + ε := sorry

example {a : ℝ} : |a| ^ 2 = a ^ 2 := sorry

/- ## Exercise 2
Show the following relations between the absolute value and `min`/`max`.
-/

lemma av_eq_max {a : ℝ} : |a| = max a (-a) := sorry

example {a b : ℝ} : max a b = (a + b + |a - b|) / 2 := sorry

example {a b : ℝ} : min a b = (a + b - |a - b|) / 2 := sorry

/- ## Exercise 3
Show the following lemmas
-/

lemma forall_eps_le {a b : ℝ} (h : ∀ ε > 0, a ≤ b + ε) : a ≤ b := sorry

lemma eq_iff_sub_lt_forall {a b : ℝ} : a = b ↔ ∀ ε > 0, |a - b| < ε := sorry

lemma av_add (a b : ℝ) : |a + b| ≤ |a| + |b| := sorry

lemma av_neg (a : ℝ) : |-a| = |a| := sorry

/- ## Exercise 4
Show that the absolute value is multiplicative.
-/
lemma av_mul (a b : ℝ) : |a * b| = |a| * |b| := sorry

/- ## Exercise 5
**Convergence**
Using the following definition of convergence and the preceding
exercises, show some basic lemmas about sequences.
-/

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

theorem ConvergesTo_thirtyseven : ConvergesTo (fun _ ↦ 37) 37 := sorry

/-- The limit of the constant sequence with value `c` is `c`. -/
theorem ConvergesTo_const (c : ℝ) : ConvergesTo (fun _ ↦ c) c := sorry

/-- If `a(n)` tends to `t` then `a(n) + c` tends to `t + c` -/
theorem ConvergesTo_add_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : ConvergesTo a t) :
    ConvergesTo (fun n => a n + c) (t + c) := sorry

/- ## Exercise 6 -/
/- Hint use `calc`.-/

theorem convergesTo_sub {s t : ℕ → ℝ} {a b : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n - t n) (a - b) := sorry

/- ## Exercise 7 -/

/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/
theorem ConvergesTo_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : ConvergesTo a t) :
    ConvergesTo (fun n ↦ 37 * a n) (37 * t) := sorry

/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem ConvergesTo_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : ConvergesTo a t) {c : ℝ} (hc : 0 < c) :
    ConvergesTo (fun n ↦ c * a n) (c * t) := sorry

/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem ConvergesTo_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : ConvergesTo a t) {c : ℝ} (hc : c < 0) :
    ConvergesTo (fun n ↦ c * a n) (c * t) := sorry

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem ConvergesTo_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : ConvergesTo a t) :
    ConvergesTo (fun n ↦ c * a n) (c * t) := sorry

/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem ConvergesTo_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : ConvergesTo a t) :
    ConvergesTo (fun n ↦ a n * c) (t * c) := sorry

/- ## Exercise 8 (*).

This exercice is a little bit harder but a good practice!
-/

/-- A sequence has at most one limit. -/
theorem ConvergesTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : ConvergesTo a s) (ht : ConvergesTo a t) :
    s = t := sorry

/- ## Exercice 9 (**)

You can try the following challenge from `Formalising Mathematics`.
You might want to prove auxiliary lemmas.
-/

example : 0.54 < Real.cos 1 ∧ Real.cos 1 < 0.55 := sorry
