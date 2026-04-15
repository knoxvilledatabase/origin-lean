/-
Extracted from Algebra/Order/BigOperators/Expect.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Order properties of the average over a finset
-/

open Function

open Fintype (card)

open scoped BigOperators Pointwise NNRat

variable {ι α R : Type*}

local notation a " /ℚ " q => (q : ℚ≥0)⁻¹ • a

namespace Finset

section OrderedAddCommMonoid

variable [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] [Module ℚ≥0 α]
  {s : Finset ι} {f g : ι → α}

lemma expect_eq_zero_iff_of_nonneg (hf : ∀ i ∈ s, 0 ≤ f i) :
    𝔼 i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0 := by
  simp +contextual [expect, sum_eq_zero_iff_of_nonneg hf]

lemma expect_eq_zero_iff_of_nonpos (hf : ∀ i ∈ s, f i ≤ 0) :
    𝔼 i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0 := by
  simp +contextual [expect, sum_eq_zero_iff_of_nonpos hf]

section PosSMulMono

variable [PosSMulMono ℚ≥0 α] {a : α}
