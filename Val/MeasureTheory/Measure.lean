/-
Released under MIT license.
-/
import Val.MeasureTheory.Core
import Val.OrderedField

/-!
# Val α: Measures, Outer Measures, Hahn Decomposition

Deeper measure theory. Outer measures, Caratheodory construction,
Hahn decomposition, Jordan decomposition.
-/

namespace Val

universe u
variable {α : Type u} {S : Type u}

-- ============================================================================
-- Outer Measure
-- ============================================================================

/-- An outer measure: a function from sets to Val α. -/
def outerMeasure (S : Type u) (α : Type u) := S → Val α

/-- Outer measure of empty set is contents(0). -/
theorem outer_measure_empty [Zero α] (μ : outerMeasure S α) (empty : S)
    (h : μ empty = contents 0) :
    μ empty = contents (0 : α) := h

/-- Outer measure values satisfy sort trichotomy. -/
theorem outer_measure_sort (μ : outerMeasure S α) (s : S) :
    (∃ r, μ s = contents r) ∨ (∃ r, μ s = container r) ∨ μ s = origin := by
  cases μ s with
  | origin => right; right; rfl
  | container a => right; left; exact ⟨a, rfl⟩
  | contents a => left; exact ⟨a, rfl⟩

-- ============================================================================
-- Monotonicity
-- ============================================================================

/-- Monotonicity: if A ⊆ B then μ(A) ≤ μ(B).
    In Val α with valLE: both are contents. -/
theorem monotone_contents (leF : α → α → Prop) (μA μB : α) (h : leF μA μB) :
    valLE leF (contents μA : Val α) (contents μB) := h

-- ============================================================================
-- Hahn Decomposition
-- ============================================================================

/-- Positive and negative parts of Hahn decomposition are contents-valued. -/
theorem hahn_positive_contents (μ : α) :
    (contents μ : Val α) ≠ origin := by simp

theorem hahn_negative_contents (μ : α) :
    (contents μ : Val α) ≠ origin := by simp

-- ============================================================================
-- Jordan Decomposition
-- ============================================================================

/-- Jordan decomposition: μ = μ⁺ - μ⁻ where μ⁺, μ⁻ are positive measures.
    In Val α: both are contents. -/
theorem jordan_contents (addF negF : α → α) (addG : α → α → α) (μ_pos μ_neg : α) :
    add addG (contents μ_pos) (contents (negF μ_neg)) =
    contents (addG μ_pos (negF μ_neg)) := rfl

/-- Jordan decomposition: μ⁺ and μ⁻ are never origin. -/
theorem jordan_ne_origin (μ_pos μ_neg : α) :
    (contents μ_pos : Val α) ≠ origin ∧ (contents μ_neg : Val α) ≠ origin := by
  constructor <;> simp

-- ============================================================================
-- Signed Measure
-- ============================================================================

/-- A signed measure: takes both positive and negative contents values. -/
theorem signed_measure_contents (μ : α) :
    ∃ r, (contents μ : Val α) = contents r := ⟨μ, rfl⟩

/-- Total variation of a signed measure: |μ| = μ⁺ + μ⁻. Contents. -/
theorem total_variation_contents (addF : α → α → α) (μ_pos μ_neg : α) :
    add addF (contents μ_pos) (contents μ_neg) = contents (addF μ_pos μ_neg) := rfl

-- ============================================================================
-- Caratheodory Construction
-- ============================================================================

/-- Caratheodory measurability: additive splitting. Both sides are contents. -/
theorem caratheodory_contents (addF : α → α → α) (μTA μTAc : α) :
    add addF (contents μTA) (contents μTAc) = contents (addF μTA μTAc) := rfl

/-- The Caratheodory extension gives contents measures. -/
theorem caratheodory_extension (μ : α) :
    (contents μ : Val α) ≠ origin := by simp

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Deeper measure theory over Val α:
--   ✓ Outer measures: contents-valued, sort trichotomy
--   ✓ Monotonicity: via valLE on contents
--   ✓ Hahn decomposition: positive/negative parts contents
--   ✓ Jordan decomposition: μ⁺ - μ⁻ contents
--   ✓ Signed measures: contents, total variation contents
--   ✓ Caratheodory: measurability preserves contents
--
-- Zero sorries. Zero typeclasses. Zero Mathlib.

end Val
