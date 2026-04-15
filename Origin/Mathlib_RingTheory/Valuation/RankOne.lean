/-
Extracted from RingTheory/Valuation/RankOne.lean
Genuine: 4 | Conflates: 0 | Dissolved: 3 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Data.NNReal.Defs
import Mathlib.RingTheory.Valuation.Basic

/-!
# Rank one valuations

We define rank one valuations.

## Main Definitions
* `RankOne` : A valuation `v` has rank one if it is nontrivial and its image is contained in `ℝ≥0`.
  Note that this class contains the data of the inclusion of the codomain of `v` into `ℝ≥0`.

## Tags

valuation, rank one
-/

noncomputable section

open Function Multiplicative

open scoped NNReal

variable {R : Type*} [Ring R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

namespace Valuation

-- DISSOLVED: RankOne

namespace RankOne

variable (v : Valuation R Γ₀) [RankOne v]

lemma strictMono : StrictMono (hom v) := strictMono'

-- DISSOLVED: nontrivial

theorem zero_of_hom_zero {x : Γ₀} (hx : hom v x = 0) : x = 0 := by
  refine (eq_of_le_of_not_lt (zero_le' (a := x)) fun h_lt ↦ ?_).symm
  have hs := strictMono v h_lt
  rw [_root_.map_zero, hx] at hs
  exact hs.false

theorem hom_eq_zero_iff {x : Γ₀} : RankOne.hom v x = 0 ↔ x = 0 :=
  ⟨fun h ↦ zero_of_hom_zero v h, fun h ↦ by rw [h, _root_.map_zero]⟩

def unit : Γ₀ˣ :=
  Units.mk0 (v (nontrivial v).choose) ((nontrivial v).choose_spec).1

-- DISSOLVED: unit_ne_one

end RankOne

end Valuation
