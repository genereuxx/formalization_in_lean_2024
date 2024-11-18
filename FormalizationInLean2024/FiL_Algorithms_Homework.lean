import FormalizationInLean2024.Defs.FiL_Algorithms_Defs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.List.Sort
import Mathlib.Data.Tree.Basic
import Mathlib.Tactic

/-
The exercices from this sheet are taken from *Functional Data Structures and Algorithms*
by Nipkow.

The reference is available online and should be consulted if you feel like you are missing context.
The number of the exercises refer to the ones from the book.
-/

/- # Homework: Algorithms -/

section LinearOrder
variable [LinearOrder α] [Inhabited α]
open List

/-
## Exercise 2.1
Consider the two following measure of complexity on insertion sort:
-/
#check List.insertionSort

def time_orderedInsert : α → List α → ℕ
| _, [] => 1
| x, (y :: ys) => (if x ≤ y then 0 else time_orderedInsert x ys) + 1

def time_insort :  List α → ℕ
| [] => 1
| (x :: xs) =>
    time_insort xs + time_orderedInsert x (xs.insertionSort (· ≤ ·)) + 1

/-
Show that `time_insort` achieves its optimal value of `2n + 1` for sorted
lists, and its worst-case value of `(n + 1)(n + 2) / 2 ` for the list `(range' 1 n).reverse`.

For the worst case, you might find it worth while to prove some lemmas beforehand.
-/

#reduce (range' 1 5).reverse
#reduce (iota 5)
#reduce time_insort (range' 1 20)
#reduce time_insort (range' 1 20).reverse

/-
## Exercise 3.1 (*)
Recall the notion of **selection**:

Given a list `xs` of length `n` with some linear order defined on its elements
and a natural number `k < n`, return the `k`-th smallest number in the list
(starting with `k = 0` for the minimal element).

A simple special case of selection is `select 0 xs`, i.e. the minimum.
Implement a linear-time function `select0` such that
`xs ≠ [] → select0 xs = select 0 xs`
and prove this. This function should be tail-recursive and traverse the list exactly
once. You need not prove the linear running time. (it should be obvious)

For your proof, you might find it worth while to spend time proving some
obvious lemmas about `select0`.
-/

end LinearOrder

#check inorder
/-
## Exercise 4.1.
Recall the function `inorder` from the lecture and the notes.
It has quadratic complexity because the running time
of `++` is linear in the length of its first argument.
Define a function `inorder2 : Tree α → List α → List α` that avoids
`++` but accumulates the result in its second parameter
via `::` only. Its running time should be linear in the size of the tree.
Prove `inorder2 t xs = inorder t ++ xs`.
-/


/-
## Exercise 4.2. (*)
Write a function `enum_tree : List α → List (Tree α)` such that
`Set (enum_tree xs) = {t | inorder t = xs}` and prove this proposition. You could
also prove that `enum_tree` produces lists of distinct elements, although that
is likely to be harder.
-/

/-
## Exercise 4.3.1 (**)
Although we focus on binary trees, arbitrarily branching trees can be
defined just as easily:
-/
inductive RTree (α : Type) : Type
| node : α → List (RTree α) → RTree α

open RTree
/-
Such trees are often called rose trees. They are a case of what we call "Nested recursion".
The goal of this exercise is to define the following
`mir : RTree α →  RTree α` that mirrors a rose tree and to prove `mir (mir t) = t`.

The section on nested recursion of this blog post will probably be of help for the
defition of `mir`:
https://lean-lang.org/blog/2024-1-11-recursive-definitions-in-lean/

For your proof, I suggest creating your own induction principle first.
-/

/-
## Exercice 4.3.2 (*)
Now define a height function `RTree.height` and show
`height_lt {a : α} {t : RTree α} {ts : List (RTree α)} : t ∈ ts → height t < height (node a ts)`

Use this to specify the termination proof in `mir` using `termination_by t => t.height`.
-/
