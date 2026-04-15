/-
Extracted from Order/Grade.lean
Genuine: 9 of 9 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Graded orders

This file defines graded orders, also known as ranked orders.

An `𝕆`-graded order is an order `α` equipped with a distinguished "grade" function `α → 𝕆` which
should be understood as giving the "height" of the elements. Usual graded orders are `ℕ`-graded,
cograded orders are `ℕᵒᵈ`-graded, but we can also grade by `ℤ`, and polytopes are naturally
`Fin n`-graded.

Visually, `grade ℕ a` is the height of `a` in the Hasse diagram of `α`.

## Main declarations

* `GradeOrder`: Graded order.
* `GradeMinOrder`: Graded order where minimal elements have minimal grades.
* `GradeMaxOrder`: Graded order where maximal elements have maximal grades.
* `GradeBoundedOrder`: Graded order where minimal elements have minimal grades and maximal
  elements have maximal grades.
* `grade`: The grade of an element. Because an order can admit several gradings, the first argument
  is the order we grade by.

## How to grade your order

Here are the translations between common references and our `GradeOrder`:
* [Stanley][stanley2012] defines a graded order of rank `n` as an order where all maximal chains
  have "length" `n` (so the number of elements of a chain is `n + 1`). This corresponds to
  `GradeBoundedOrder (Fin (n + 1)) α`.
* [Engel][engel1997]'s ranked orders are somewhere between `GradeOrder ℕ α` and
  `GradeMinOrder ℕ α`, in that he requires `∃ a, IsMin a ∧ grade ℕ a = 0` rather than
  `∀ a, IsMin a → grade ℕ a = 0`. He defines a graded order as an order where all minimal elements
  have grade `0` and all maximal elements have the same grade. This is roughly a less bundled
  version of `GradeBoundedOrder (Fin n) α`, assuming we discard orders with infinite chains.

## Implementation notes

One possible definition of graded orders is as the bounded orders whose flags (maximal chains)
all have the same finite length (see Stanley p. 99). However, this means that all graded orders must
have minimal and maximal elements and that the grade is not data.

Instead, we define graded orders by their grade function, without talking about flags yet.

## References

* [Konrad Engel, *Sperner Theory*][engel1997]
* [Richard Stanley, *Enumerative Combinatorics*][stanley2012]
-/

open Nat OrderDual

variable {𝕆 ℙ α β : Type*}

class GradeOrder (𝕆 α : Type*) [Preorder 𝕆] [Preorder α] where
  /-- The grading function. -/
  protected grade : α → 𝕆
  /-- `grade` is strictly monotonic. -/
  grade_strictMono : StrictMono grade
  /-- `grade` preserves `CovBy`. -/
  covBy_grade ⦃a b : α⦄ : a ⋖ b → grade a ⋖ grade b

class GradeMinOrder (𝕆 α : Type*) [Preorder 𝕆] [Preorder α] extends GradeOrder 𝕆 α where
  /-- Minimal elements have minimal grades. -/
  isMin_grade ⦃a : α⦄ : IsMin a → IsMin (grade a)

class GradeMaxOrder (𝕆 α : Type*) [Preorder 𝕆] [Preorder α] extends GradeOrder 𝕆 α where
  /-- Maximal elements have maximal grades. -/
  isMax_grade ⦃a : α⦄ : IsMax a → IsMax (grade a)

class GradeBoundedOrder (𝕆 α : Type*) [Preorder 𝕆] [Preorder α] extends GradeMinOrder 𝕆 α,
  GradeMaxOrder 𝕆 α

section Preorder -- grading

variable [Preorder 𝕆]

section Preorder -- graded order

variable [Preorder α]

section GradeOrder

variable (𝕆)

variable [GradeOrder 𝕆 α] {a b : α}

def grade : α → 𝕆 :=
  GradeOrder.grade

protected theorem CovBy.grade (h : a ⋖ b) : grade 𝕆 a ⋖ grade 𝕆 b :=
  GradeOrder.covBy_grade h

variable {𝕆}

theorem grade_strictMono : StrictMono (grade 𝕆 : α → 𝕆) :=
  GradeOrder.grade_strictMono

theorem covBy_iff_lt_covBy_grade : a ⋖ b ↔ a < b ∧ grade 𝕆 a ⋖ grade 𝕆 b :=
  ⟨fun h => ⟨h.1, h.grade _⟩,
    And.imp_right fun h _ ha hb => h.2 (grade_strictMono ha) <| grade_strictMono hb⟩

end GradeOrder

section GradeMinOrder

variable (𝕆)

variable [GradeMinOrder 𝕆 α] {a : α}

protected theorem IsMin.grade (h : IsMin a) : IsMin (grade 𝕆 a) :=
  GradeMinOrder.isMin_grade h

variable {𝕆}
