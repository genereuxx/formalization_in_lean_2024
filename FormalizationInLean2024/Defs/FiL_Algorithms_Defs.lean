import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.List.Sort
import Mathlib.Data.Tree.Basic
import Mathlib.Tactic

/- # Homework: Algorithms -/


variable {α}

def inorder : Tree α → List α
| Tree.nil => []
| Tree.node x l r => inorder l ++ [x] ++ inorder r

#eval inorder (Tree.node 1 Tree.nil (Tree.node 2 Tree.nil Tree.nil))

lemma List.get!_le_len [Inhabited α] {xs : List α} {k : ℕ} (hk : k < xs.length) :
    xs[k]! = xs[k] := by
  induction xs generalizing k
  · contradiction
  · cases k <;> aesop

section select

variable [LinearOrder α]

abbrev List.sort :
  List α → List α := List.mergeSort' (· ≤ ·)

#eval [2,1,3,5,4].sort

#eval [2,1].sort[0]!

open List

/-
Proof of Theorem 3.1.
-/
theorem select_unique {xs : List α} {k : ℕ} {x y : α} (hk : k < xs.length)
    (hx1 : (xs.filter (· < x)).length ≤ k)
    (hy1 : (xs.filter (· < y)).length ≤ k)
    (hx2 : (xs.filter (x < ·)).length < xs.length - k)
    (hy2 : (xs.filter (y < ·)).length < xs.length - k) :
    x = y := by
  by_contra h
  wlog hle : x < y
  · simp [← lt_or_lt_iff_ne, hle] at h
    exact this hk hy1 hx1 hy2 hx2 (ne_of_lt h) h
  · simp_all only [← countP_eq_length_filter]
    apply lt_irrefl xs.length
    calc
      xs.length
      = xs.countP (· ≤ x) + xs.countP (x < ·) := by simp [length_eq_countP_add_countP (· ≤ x)]
    _ ≤ (xs.countP (· < y))  + (xs.countP (x < ·)) := by
      aesop (add safe apply [countP_mono_left, lt_of_le_of_lt])
    _ < k + (xs.length - k) := by linarith
    _ = xs.length := by omega

variable [Inhabited α]

def List.select (k : ℕ) (xs : List α) : α := xs.sort[k]!

/-
Here we prove Theorem 3.2.
-/
theorem select_prop1 {xs : List α} {k : ℕ} (hk : k < xs.length) :
    (xs.filter (· < xs.select k)).length ≤ k := by
  simp_rw [← countP_eq_length_filter] at *
  wlog hsorted : Sorted (· ≤ ·) xs
  · replace this := this (by simpa) (List.sorted_mergeSort' (· ≤ ·) xs)
    simp_rw [select, sort, List.mergeSort'_eq_self _ (List.sorted_mergeSort' _ xs)] at this
    convert this using 1
    rw [List.Perm.countP_eq _ (List.perm_mergeSort' _ xs), select]
  · nth_rw 3 [← List.take_append_drop k xs]
    have hzero : countP (fun x ↦ decide (x < select k xs)) (drop k xs) = 0 := by
      rw [List.countP_eq_zero]
      intro a ha
      simp_all only [decide_eq_true_eq, not_lt, select, sort, List.mergeSort'_eq_self _ hsorted]
      induction xs generalizing k
      · aesop
      · cases k <;> aesop
    simp only [List.countP_append, hzero, add_zero]
    exact le_trans (List.countP_le_length _) (List.length_take_le _ _)

theorem select_prop2 {xs : List α} {k : ℕ} (hk : k < xs.length) :
    (xs.filter (xs.select k < ·)).length < xs.length - k := by
  simp_rw [← countP_eq_length_filter] at *
  wlog hsorted : Sorted (· ≤ · ) xs
  · replace this := this (by simpa) (List.sorted_mergeSort' (· ≤ ·) xs)
    simp_rw [select, sort,
      List.mergeSort'_eq_self (· ≤ ·) (List.sorted_mergeSort' (· ≤ ·) xs)] at this
    convert this using 1
    · rw [List.Perm.countP_eq _ (List.perm_mergeSort' _ xs), select]
    rw [length_mergeSort']
  · nth_rw 3 [← List.take_append_drop (k + 1) xs]
    simp only [List.countP_append]
    have hzero : countP (fun x ↦ decide (select k xs < x)) (take (k + 1) xs) = 0 := by
      rw [List.countP_eq_zero]
      intro a ha
      simp_all only [decide_eq_true_eq, not_lt, select, sort]
      rw [List.mergeSort'_eq_self _ hsorted]
      induction xs generalizing k
      · aesop
      · rcases k with - | k
        · simp_all
        simp_all only [sorted_cons, length_cons, add_lt_add_iff_right, take_succ_cons,
          mem_cons, getElem!_cons_succ, true_implies]
        obtain ⟨left, -⟩ := hsorted
        rcases ha
        · rw [List.get!_le_len hk]
          aesop (add forward safe List.getElem_mem)
        · simp_all only
    simp only [List.countP_append, hzero, zero_add]
    rw [Nat.lt_iff_le_pred (by omega), ← Nat.sub_add_eq, ← List.length_drop (k+1)]
    exact (List.countP_le_length _)
