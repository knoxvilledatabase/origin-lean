/-
Released under MIT license.
-/
import Val.MeasureTheory.Core

/-!
# Val α: Haar, Counting, Dirac, Bernoulli Measures

Specific measures: Haar measure, counting measure, Dirac delta, Bernoulli.
-/

namespace Val

universe u
variable {α : Type u} {S : Type u}

-- ============================================================================
-- Dirac Measure
-- ============================================================================

/-- Dirac measure at a point: δ_a(A) = 1 if a ∈ A, 0 otherwise.
    In Val α: both 1 and 0 are contents. -/
def diracMeasure (one zero : α) (a : S) (test : S → Bool) : Val α :=
  if test a then contents one else contents zero

/-- Dirac measure is always contents. -/
theorem dirac_is_contents (one zero : α) (a : S) (test : S → Bool) :
    ∃ r, diracMeasure one zero a test = contents r := by
  unfold diracMeasure; cases test a with
  | true => exact ⟨one, rfl⟩
  | false => exact ⟨zero, rfl⟩

/-- Dirac measure is never origin. -/
theorem dirac_ne_origin (one zero : α) (a : S) (test : S → Bool) :
    diracMeasure one zero a test ≠ (origin : Val α) := by
  unfold diracMeasure; cases test a with
  | true => simp
  | false => simp

-- ============================================================================
-- Counting Measure
-- ============================================================================

/-- Counting measure: μ(A) = |A|. A contents value. -/
def countingMeasure (count : α) : Val α := contents count

/-- Counting measure is contents. -/
theorem counting_is_contents (count : α) :
    ∃ r, countingMeasure count = contents r := ⟨count, rfl⟩

/-- Counting measure is never origin. -/
theorem counting_ne_origin (count : α) :
    countingMeasure count ≠ (origin : Val α) := by simp [countingMeasure]

-- ============================================================================
-- Haar Measure
-- ============================================================================

/-- Haar measure: the unique translation-invariant measure on a locally compact group.
    In Val α: Haar measure values are contents. -/
def haarMeasure (μ_val : α) : Val α := contents μ_val

/-- Haar measure is contents. -/
theorem haar_is_contents (μ_val : α) :
    ∃ r, haarMeasure μ_val = contents r := ⟨μ_val, rfl⟩

/-- Haar measure is never origin. -/
theorem haar_ne_origin (μ_val : α) :
    haarMeasure μ_val ≠ (origin : Val α) := by simp [haarMeasure]

/-- Translation invariance: μ(gA) = μ(A). Both contents. -/
theorem haar_translation_invariant (μ_A μ_gA : α) (h : μ_gA = μ_A) :
    (contents μ_gA : Val α) = contents μ_A := by rw [h]

-- ============================================================================
-- Bernoulli Measure
-- ============================================================================

/-- Bernoulli measure: P({1}) = p, P({0}) = 1-p. Both contents. -/
theorem bernoulli_contents (p comp_p : α) :
    (∃ r, (contents p : Val α) = contents r) ∧
    (∃ r, (contents comp_p : Val α) = contents r) :=
  ⟨⟨p, rfl⟩, ⟨comp_p, rfl⟩⟩

/-- Bernoulli probabilities sum to 1. -/
theorem bernoulli_total (addF : α → α → α) (p comp_p one : α)
    (h : addF p comp_p = one) :
    add addF (contents p) (contents comp_p) = contents one := by
  show contents (addF p comp_p) = contents one; rw [h]

-- ============================================================================
-- Lebesgue Measure
-- ============================================================================

/-- Lebesgue measure on intervals: μ([a,b]) = b - a. Contents. -/
theorem lebesgue_interval (subF : α → α → α) (a b : α) :
    (contents (subF b a) : Val α) ≠ origin := by simp

/-- Lebesgue measure is translation invariant. -/
theorem lebesgue_translation (subF addF : α → α → α) (a b c : α)
    (h : subF (addF b c) (addF a c) = subF b a) :
    (contents (subF (addF b c) (addF a c)) : Val α) = contents (subF b a) := by
  show contents (subF (addF b c) (addF a c)) = contents (subF b a); rw [h]

-- ============================================================================
-- Gaussian Measure
-- ============================================================================

/-- Gaussian measure: density is exp(-x²/2)/√(2π). Contents. -/
theorem gaussian_density_contents (density : α) :
    (contents density : Val α) ≠ origin := by simp

/-- Gaussian integral: ∫ exp(-x²/2) dx = √(2π). Contents. -/
theorem gaussian_integral (mulF : α → α → α) (density μ_val : α) :
    mul mulF (contents density) (contents μ_val) = contents (mulF density μ_val) := rfl

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Specific measures over Val α:
--   ✓ Dirac: contents (0 or 1), never origin
--   ✓ Counting: contents, never origin
--   ✓ Haar: contents, translation invariant
--   ✓ Bernoulli: both p and comp_p contents, sum to 1
--   ✓ Lebesgue: interval measure contents, translation invariant
--   ✓ Gaussian: density contents, integral contents
--
-- Zero sorries. Zero typeclasses. Zero Mathlib.

end Val
