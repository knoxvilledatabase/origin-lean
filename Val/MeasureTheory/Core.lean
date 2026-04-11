/-
Released under MIT license.
-/
import Val.Algebra

/-!
# Measure Theory on Val α

Measures, null sets, integration. The key disambiguation:
`contents(0)` is measure zero. `origin` is the boundary.
In standard math both are written 0. Val α makes the sorts visible.
-/

namespace Val

universe u
variable {α : Type u}
variable {S : Type u}  -- index type for measurable sets

-- ============================================================================
-- Measures
-- ============================================================================

/-- A contents measure assigns contents values to every set. -/
def isContentsMeasure (μ : S → Val α) : Prop :=
  ∀ s : S, ∃ a : α, μ s = contents a

-- ============================================================================
-- Null Sets: contents(0), Not Origin
-- ============================================================================

/-- A set is null when its measure is contents(zero). NOT origin. -/
def isNull (μ : S → Val α) (zero : α) (s : S) : Prop :=
  μ s = contents zero

/-- Null sets are not origin. Measure zero ≠ boundary. -/
theorem null_ne_origin (μ : S → Val α) (zero : α) (s : S)
    (h : isNull μ zero s) : μ s ≠ origin := by
  rw [h]; simp

/-- Null sets are not container. -/
theorem null_ne_container (μ : S → Val α) (zero : α) (s : S) (c : α)
    (h : isNull μ zero s) : μ s ≠ container c := by
  rw [h]; simp

-- ============================================================================
-- Countable Additivity Within Contents
-- ============================================================================

/-- Finite additivity: μ(A) + μ(B) is contents when both are contents. -/
theorem finite_additivity_contents (addF : α → α → α)
    (μ : S → Val α) (a b : S) (va vb : α)
    (ha : μ a = contents va) (hb : μ b = contents vb) :
    add addF (μ a) (μ b) = contents (addF va vb) := by
  rw [ha, hb]; rfl

/-- Finite additivity result is never origin. -/
theorem finite_additivity_ne_origin (addF : α → α → α)
    (μ : S → Val α) (a b : S) (va vb : α)
    (ha : μ a = contents va) (hb : μ b = contents vb) :
    add addF (μ a) (μ b) ≠ origin := by
  rw [ha, hb]; simp

-- ============================================================================
-- Almost Everywhere
-- ============================================================================

/-- A property holds a.e. when the exception set is null.
    The exception has measure contents(zero) — not origin. -/
def almostEverywhere (μ : S → Val α) (zero : α) (exception : S) : Prop :=
  isNull μ zero exception

/-- Almost everywhere exception is not origin. -/
theorem ae_ne_origin (μ : S → Val α) (zero : α) (exc : S)
    (h : almostEverywhere μ zero exc) : μ exc ≠ origin :=
  null_ne_origin μ zero exc h

-- ============================================================================
-- Radon-Nikodym: No ≠ 0 Hypothesis
-- ============================================================================

/-- Radon-Nikodym derivative: dμ/dν is contents. No hypothesis on ν. -/
theorem radon_nikodym_contents (mulF : α → α → α) (invF : α → α)
    (μ_val ν_val : α) :
    mul mulF (contents μ_val) (inv invF (contents ν_val)) =
    contents (mulF μ_val (invF ν_val)) := rfl

/-- Radon-Nikodym derivative is never origin. -/
theorem radon_nikodym_ne_origin (mulF : α → α → α) (invF : α → α)
    (μ_val ν_val : α) :
    mul mulF (contents μ_val) (inv invF (contents ν_val)) ≠ origin := by
  simp

-- ============================================================================
-- Integration Within Contents
-- ============================================================================

/-- Simple integral step: value × measure = contents. -/
theorem simple_integral_step (mulF : α → α → α) (value measure_val : α) :
    mul mulF (contents value) (contents measure_val) =
    contents (mulF value measure_val) := rfl

/-- Integration accumulation stays in contents at every step. -/
theorem integral_accumulate (addF mulF : α → α → α)
    (running value measure_val : α) :
    add addF (contents running)
             (mul mulF (contents value) (contents measure_val)) =
    contents (addF running (mulF value measure_val)) := rfl

-- ============================================================================
-- σ-Finiteness
-- ============================================================================

/-- A contents measure over a countable cover never produces origin. -/
theorem sigma_finite_contents (μ : S → Val α)
    (cover : Nat → S)
    (h : ∀ n, ∃ a : α, μ (cover n) = contents a) :
    ∀ n, μ (cover n) ≠ origin := by
  intro n
  obtain ⟨a, ha⟩ := h n
  rw [ha]; simp

-- ============================================================================
-- Origin Absorption in Measure Computations
-- ============================================================================

/-- Origin absorbs in measure addition. -/
theorem measure_origin_absorbs (addF : α → α → α) (a : α) :
    add addF origin (contents a) = origin := by simp

/-- Origin absorbs in integration. -/
theorem integral_origin_absorbs (mulF : α → α → α) (a : α) :
    mul mulF (contents a) origin = origin := by simp

end Val
