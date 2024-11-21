import FiL.LoVelib
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Sort

open List
set_option linter.unusedSectionVars false
variable [LinearOrder α]

/- # Algorithms -/

/-
The material from this demo is based on Nipkow's
**Functional Data Structures and Algorithms**

We look at the beginning of chapter 2, 3 and 4.
Goals :
- Use `aesop` to automate some parts of the proofs.
- Induction with `generalize` keyword.
-/

/-
## Intro
The first algorithmic problem we will consider is the problem
of sorted lists.

During this demo, we will focus on insertion sort.
We will also analyse its running time.
-/

/-## Concept of sorted list -/

abbrev List.sort :
  List α → List α := sorry

#print List.Sorted

/-
`List.Pairwise R l` means that all the elements with earlier indexes are
`R`-related to all the elements with later indexes.
```
Pairwise R [1, 2, 3] ↔ R 1 2 ∧ R 1 3 ∧ R 2 3
```
For example if `R = (·≠·)` then it asserts `l` has no duplicates,
and if `R = (·<·)` then it asserts that `l` is (strictly) sorted.
-/
namespace FiL

inductive Pairwise (R : α → α → Prop) : List α → Prop
  /-- All elements of the empty list are vacuously pairwise related. -/
  | nil : Pairwise R []
  /-- `a :: l` is `Pairwise R` if `a` `R`-relates to every element of `l`,
  and `l` is `Pairwise R`. -/
  | cons : ∀ {a : α} {l : List α}, (∀ a', a' ∈ l → R a a') →
    Pairwise R l → Pairwise R (a :: l)

end FiL
/-
## Linear Order
The book assumes that we have a linear order on our type `α`.
-/
#check LinearOrder

/-
- reflexivity: `x ≤ x`
- transitivity: `x ≤ y ∧ y ≤ z → x ≤ z`
- antisymmetry: `a ≤ b ∧ b ≤ a → a = b`
- linearity/totality: `x ≤ y ∨ y ≤ x`
-/

/-
This means that we can't use `linarith`.
You will need to provide the proofs yourself. (Or use `aesop`)
-/

/-
## Properties of sorting algorithms

If `sort` is a sorting function, we want
-/
example (l : List α) : List.Sorted (· ≤ ·) (l.sort) := sorry

/-
This is not enough we also need the notion that the sorted list
contains exactly the same elements :
-/

example (l : List α) : Multiset.ofList l.sort = Multiset.ofList l := sorry

example (l : List α) : l.sort ~ l := sorry

/-
## Insertion Sort
-/
namespace FiL

@[simp]
def orderedInsert (a : α) : List α → List α
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: orderedInsert a l

/-- `insertionSort l` returns `l` sorted using the
  insertion sort algorithm. -/
@[simp]
def insertionSort : List α → List α
  | [] => []
  | b :: l => orderedInsert b (insertionSort l)

#reduce insertionSort [5, 1, 4, 4, 5, 0]

/-
We can prove some functional properties by induction/recursion.
-/

theorem perm_orderedInsert (a : α) (l : List α) :
  orderedInsert a l ~ a :: l := by
  match l with
  | [] => simp only [orderedInsert, Perm.refl]
  | x :: xs =>
    by_cases this : a ≤ x
    · simp [this]
    · simp only [orderedInsert, this, ↓reduceIte]
      obtain ih := perm_orderedInsert a xs
      replace ih := ih.cons x
      apply Perm.trans ih
      exact (Perm.swap _ _ _)

theorem perm_insertionSort (l : List α) : insertionSort l ~ l := by
  match l with
  | [] => simp
  | x :: xs =>
    simp only [insertionSort]
    obtain ih := perm_insertionSort xs
    apply Perm.trans (perm_orderedInsert x (insertionSort xs))
    exact ih.cons x

def Sorted := _root_.List.Sorted (α := α) (· ≤ ·)

theorem sorted_orderedInsert (a : α) (l : List α) (hl : Sorted l) :
    Sorted (orderedInsert a l) := by
  induction hl with
  | nil => simp only [Sorted, orderedInsert, sorted_singleton];
  | cons ih ih' hle =>
    aesop? (add norm [Sorted])
    · exact le_trans h (ih _ a_3)
    · induction' l_1 with y ys
      · aesop (add safe le_of_lt)
      · aesop (add safe forward le_of_lt, unsafe le_trans)


    /-simp_all only [Sorted, orderedInsert]
    split
    next x xs h =>
      simp_all only [sorted_cons, mem_cons, forall_eq_or_imp,
        true_and, implies_true]
      apply And.intro
      · intro a_2 a_3
        exact le_trans h (ih _ a_3)
      · exact ih'
    next x xs h =>
      simp_all only [not_le, sorted_cons, and_true]
      intro b a_2
      induction' xs with y ys
      · aesop (add safe le_of_lt)
      · aesop (add safe forward le_of_lt, unsafe le_trans)-/


theorem sorted_insertionSort : ∀ l : List α, Sorted (insertionSort l)
  | [] => sorted_nil
  | a :: l => sorted_orderedInsert a _ (FiL.sorted_insertionSort l)

/-
### Running Time analysis
-/

def time_orderedInsert : α → List α → ℕ
| _, [] => 1
| x, (y :: ys) => (if x ≤ y then 0 else time_orderedInsert x ys) + 1

def time_insort :  List α → ℕ
| [] => 1
| (x :: xs) =>
    time_insort xs + time_orderedInsert x (xs.insertionSort (· ≤ ·)) + 1

/-
A "dismal" quadratic upper bound for the running time of insertion
sort is proved readily:

**Lemma 2.1.** `time_insort l ≤ (l.length + 1) ^ 2`
Proof. The following properties are proved by induction on xs :

`time_orderedInsert x xs ≤ xs.length + 1` (2.6)
`(orderedInsert x xs).length = xs.length + 1` (2.7)
`(insertionSort xs).length = xs.length` (2.8)
The proof of (2.8) needs (2.7). The proof of the lemma is also by
induction on xs.

The base case is trivial. The induction step is easy :

`time_insort (x :: xs) = time_insort xs + time_orderedInsert x (insertionSort xs) + 1`
` _ ≤ (xs.lenght + 1) ^ 2 + time_orderedInsert x (insertionSort xs) + 1 `:= by IH
` _ ≤ (xs.length + 1) ^ 2 + xs.lenght + 1 + 1` := using (2.6) and (2.8)
` _ ≤ ((x :: xs).length + 1) ^ 2` := linarith?
-/

theorem time_orderedInsert_le_len (x : α) (xs : List α) :
    time_orderedInsert x xs ≤ xs.length + 1 := by
  match xs with
  | [] => aesop
  | y :: ys => aesop (add norm time_orderedInsert, safe time_orderedInsert_le_len)

@[simp]
theorem len_orderedInsert (x : α) (xs : List α) :
    (orderedInsert x xs).length = xs.length + 1 := by
  match xs with
  | [] => aesop
  | y :: ys => aesop (add norm orderedInsert, safe len_orderedInsert)

@[simp]
theorem len_insort (x : α) (xs : List α) :
    (insertionSort xs).length = xs.length := by
  match xs with
  | [] => aesop
  | y :: ys => aesop (add norm [orderedInsert], safe len_insort)

example (l : List α) : time_insort l ≤ (l.length + 1) ^ 2 := by
  induction l with
  | nil => aesop
  | cons x xs ih =>
    simp_all only [time_insort, length_cons]
    calc
     time_insort xs + time_orderedInsert x (xs.insertionSort (· ≤ ·)) + 1 ≤
      (xs.length + 1) ^ 2 + time_orderedInsert x (xs.insertionSort (· ≤ ·)) + 1 := by
        aesop
    _ ≤ (xs.length + 1) ^ 2 + (xs.length + 1) + 1 := by
      simp_all only [add_le_add_iff_right, add_le_add_iff_left]
      apply le_trans (time_orderedInsert_le_len _ _) (by aesop)
    _ ≤ (xs.length + 1 + 1) ^ 2 := by linarith


end FiL

/-
# Selection

Before we look at selection, let's first let's look at some of the tools we have for lists.
-/

#check List.filter
#check List.countP
#check List.countP_eq_length_filter


/- **Selection**
Given a list `xs` of length `n` with some linear order defined on its elements
and a natural number `k < n`, return the `k`-th smallest number in the list
(starting with `k = 0` for the minimal element).
-/


def List.select' (k : ℕ) (xs : List α) : α := sorry

/-
We can caracterise the notion of selection in the following way :

  Let `k < xs.length` then `select k xs` is such that there are at
  most `k` elements that are strictly smaller and `n - k` that are
  strictly bigger.

In other "words",
-/

example {xs : List α} {k : ℕ} (hk : k < xs.length) :
    (xs.filter (· < (xs.select' k))).length ≤ k
    ∧ (xs.filter ((xs.select' k) < ·)).length < xs.length - k := sorry

/-
These properties fully specify the `select` operation.
We get this by showing that the value `(xs.select' k)` has to be unique in this setting. -/

theorem select_unique {xs : List α} {k : ℕ} {x y : α} (hk : k < xs.length)
    (hx1 : (xs.filter (· < x)).length ≤ k)
    (hy1 : (xs.filter (· < y)).length ≤ k)
    (hx2 : (xs.filter (x < ·)).length < xs.length - k)
    (hy2 : (xs.filter (y < ·)).length < xs.length - k) :
    x = y := by
  by_contra h
  /- We save some work by using `wlog` -/
  wlog hle : x < y -- generalizing x y
  · simp [← lt_or_lt_iff_ne, hle] at h
    exact this hk hy1 hx1 hy2 hx2 (ne_of_lt h) h
  · simp_all only [← countP_eq_length_filter]
    apply lt_irrefl xs.length
    calc
      xs.length
      = xs.countP (· ≤ x) + xs.countP (x < ·) := by
        simp [length_eq_countP_add_countP (· ≤ x)]
    _ ≤ (xs.countP (· < y))  + (xs.countP (x < ·)) := by
      aesop (add safe apply [countP_mono_left, lt_of_le_of_lt])
    _ < k + (xs.length - k) := by linarith
    _ = xs.length := by omega

variable [Inhabited α]

def List.select (k : ℕ) (xs : List α) : α := xs.sort[k]!

/-
Example of a lemma needed to prove the properties.
(Note : This is because `xs[k]` has some ncie lemmas that we *sometimes* want to access.)

Example of : `induction xs generalizing k`.
-/
lemma List.get!_le_len {xs : List α} {k : ℕ} (hk : k < xs.length) :
    xs[k]! = xs[k] := by
  induction xs generalizing k
  · contradiction
  · rename_i x xs ih
    rcases k with - | n
    · simp_all only [getElem!_cons_zero, getElem_cons_zero]
    · simp_all only [getElem!_cons_succ, getElem_cons_succ]
      exact ih (Nat.lt_of_succ_lt_succ hk)

/-
Remark : you can also achieve this using recurrence.
-/

theorem select_prop1 {xs : List α} {k : ℕ} (hk : k < xs.length) :
    (xs.filter (· < xs.select k)).length ≤ k := by sorry

theorem select_prop2 {xs : List α} {k : ℕ} (hk : k < xs.length) :
    (xs.filter (xs.select k < ·)).length < xs.length - k := by sorry

/-
# Trees
-/
namespace FiL

inductive Tree (α : Type u) : Type u
  | nil : Tree α
  | node : α → Tree α → Tree α → Tree α

#check Tree.node 1 Tree.nil (Tree.node 2 Tree.nil Tree.nil)

namespace Tree

def toSet : Tree α → Finset α
  | .nil => ∅
  | .node x r l => r.toSet ∪ {x} ∪ l.toSet

def map {β} (f : α → β) : Tree α → Tree β
  | nil => nil
  | node a l r => node (f a) (map f l) (map f r)

def inorder : Tree α → List α
| Tree.nil => []
| Tree.node x l r => inorder l ++ [x] ++ inorder r

#eval inorder (Tree.node 1 Tree.nil (Tree.node 2 Tree.nil Tree.nil))

def numNodes : Tree α → ℕ
  | nil => 0
  | node _ a b => a.numNodes + b.numNodes + 1

@[simp]
def numLeaves : Tree α → ℕ
  | nil => 1
  | node _ a b => a.numLeaves + b.numLeaves

theorem numLeaves_eq_numNodes_succ (x : Tree α) : x.numLeaves = x.numNodes + 1 := by
  match x with
  | nil => simp only [Tree.numLeaves, Tree.numNodes, zero_add]
  | node _ l r =>
    simp only [Tree.numLeaves, Tree.numNodes]
    rw [numLeaves_eq_numNodes_succ l]
    rw [numLeaves_eq_numNodes_succ r]
    omega

@[simp]
def height : Tree α → ℕ
  | nil => 0
  | node _ a b => max a.height b.height + 1

theorem num_Leaves_le_pow_height (x : Tree α) : x.numLeaves ≤ 2 ^ (x.height) := by
  match x with
  | nil => simp
  | node _ l r =>
    simp only [numLeaves, height, ge_iff_le]
    apply le_trans (add_le_add (num_Leaves_le_pow_height l) (num_Leaves_le_pow_height r))
    apply le_trans (add_le_add (pow_le_pow_right (by omega) (le_max_left _ r.height))
      (pow_le_pow_right (by omega) (le_max_right l.height _)))
    omega
