/-
Extracted from Algebra/Order/Ring/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Basic lemmas about ordered rings
-/

assert_not_exists Set.Subsingleton

open Function Int

variable {α M R : Type*}

theorem IsSquare.nonneg [Semiring R] [LinearOrder R]
    [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R]
    {x : R} (h : IsSquare x) : 0 ≤ x := by
  rcases h with ⟨y, rfl⟩
  exact mul_self_nonneg y
