/-
Extracted from Order/KrullDimension.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Krull dimension of a preordered set and height of an element

If `α` is a preordered set, then `krullDim α : WithBot ℕ∞` is defined to be
`sup {n | a₀ < a₁ < ... < aₙ}`.

In case that `α` is empty, then its Krull dimension is defined to be negative infinity; if the
length of all series `a₀ < a₁ < ... < aₙ` is unbounded, then its Krull dimension is defined to be
positive infinity.

For `a : α`, its height (in `ℕ∞`) is defined to be `sup {n | a₀ < a₁ < ... < aₙ ≤ a}`, while its
coheight is defined to be `sup {n | a ≤ a₀ < a₁ < ... < aₙ}` .

## Main results

* The Krull dimension is the same as that of the dual order (`krullDim_orderDual`).

* The Krull dimension is the supremum of the heights of the elements (`krullDim_eq_iSup_height`),
  or their coheights (`krullDim_eq_iSup_coheight`), or their sums of height and coheight
  (`krullDim_eq_iSup_height_add_coheight_of_nonempty`)

* The height in the dual order equals the coheight, and vice versa.

* The height is monotone (`height_mono`), and strictly monotone if finite (`height_strictMono`).

* The coheight is antitone (`coheight_anti`), and strictly antitone if finite
  (`coheight_strictAnti`).

* The height is the supremum of the successor of the height of all smaller elements
  (`height_eq_iSup_lt_height`).

* The elements of height zero are the minimal elements (`height_eq_zero`), and the elements of
  height `n` are minimal among those of height `≥ n` (`height_eq_coe_iff_minimal_le_height`).

* Concrete calculations for the height, coheight and Krull dimension in `ℕ`, `ℤ`, `WithTop`,
  `WithBot` and `ℕ∞`.

## Design notes

Krull dimensions are defined to take value in `WithBot ℕ∞` so that `(-∞) + (+∞)` is
also negative infinity. This is because we want Krull dimensions to be additive with respect
to product of varieties so that `-∞` being the Krull dimension of empty variety is equal to
sum of `-∞` and the Krull dimension of any other varieties.

We could generalize the notion of Krull dimension to an arbitrary binary relation; many results
in this file would generalize as well. But we don't think it would be useful, so we only define
Krull dimension of a preorder.
-/

assert_not_exists Field

namespace Order

section definitions

noncomputable def krullDim (α : Type*) [Preorder α] : WithBot ℕ∞ :=
  ⨆ (p : LTSeries α), p.length

noncomputable def height {α : Type*} [Preorder α] (a : α) : ℕ∞ :=
  ⨆ (p : LTSeries α) (_ : p.last ≤ a), p.length

noncomputable def coheight {α : Type*} [Preorder α] (a : α) : ℕ∞ := height (α := αᵒᵈ) a

end definitions

/-!
## Height
-/

section height

variable {α β : Type*}

variable [Preorder α] [Preorder β]
