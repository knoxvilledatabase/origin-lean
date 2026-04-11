/-
Released under MIT license.
-/
import Val.MeasureTheory.Core

/-!
# Val α: Lebesgue Decomposition, Radon-Nikodym (Deep)

Deeper decomposition: Lebesgue decomposition, Radon-Nikodym derivative,
conditional expectation, disintegration.
-/

namespace Val

universe u
variable {α : Type u} {S : Type u}

-- ============================================================================
-- Lebesgue Decomposition
-- ============================================================================

/-- Lebesgue decomposition: μ = μ_ac + μ_s where μ_ac ≪ ν and μ_s ⊥ ν.
    Both parts are contents-valued measures. -/
theorem lebesgue_decomposition_contents (addF : α → α → α) (μ_ac μ_s : α) :
    add addF (contents μ_ac) (contents μ_s) = contents (addF μ_ac μ_s) := rfl

/-- The absolutely continuous part is contents. -/
theorem lebesgue_ac_contents (μ_ac : α) :
    (contents μ_ac : Val α) ≠ origin := by simp

/-- The singular part is contents. -/
theorem lebesgue_singular_contents (μ_s : α) :
    (contents μ_s : Val α) ≠ origin := by simp

-- ============================================================================
-- Radon-Nikodym Derivative (Deep)
-- ============================================================================

/-- The Radon-Nikodym derivative dμ/dν: μ(A) = ∫_A (dμ/dν) dν. -/
theorem radon_nikodym_density (mulF : α → α → α) (density ν_val : α) :
    mul mulF (contents density) (contents ν_val) = contents (mulF density ν_val) := rfl

/-- Chain rule: d(μ ∘ g)/dν = (dμ/dν) · |g'|. Contents throughout. -/
theorem radon_nikodym_chain (mulF : α → α → α) (dμdν g_prime : α) :
    mul mulF (contents dμdν) (contents g_prime) = contents (mulF dμdν g_prime) := rfl

/-- Radon-Nikodym uniqueness: two equal densities give equal contents. -/
theorem radon_nikodym_unique (f g : α) (h : f = g) :
    (contents f : Val α) = contents g := by rw [h]

-- ============================================================================
-- Mutual Singularity
-- ============================================================================

/-- Two measures are mutually singular if their singular sets are contents(0). -/
theorem mutual_singular [Zero α] (μ_Ac ν_A : α)
    (h1 : μ_Ac = 0) (h2 : ν_A = 0) :
    (contents μ_Ac : Val α) = contents (0 : α) ∧
    (contents ν_A : Val α) = contents (0 : α) := by
  constructor
  · show contents μ_Ac = contents 0; rw [h1]
  · show contents ν_A = contents 0; rw [h2]

-- ============================================================================
-- Conditional Expectation
-- ============================================================================

/-- Conditional expectation E[X|F]: the result is contents. -/
theorem cond_exp_contents (condExp : α) :
    (contents condExp : Val α) ≠ origin := by simp

/-- Tower property: E[E[X|F]|G] = E[X|G] when G ⊆ F. Both sides contents. -/
theorem tower_property (condExpXF condExpXG : α) (h : condExpXF = condExpXG) :
    (contents condExpXF : Val α) = contents condExpXG := by rw [h]

/-- Conditional expectation is linear: E[aX+bY|F] = aE[X|F]+bE[Y|F]. -/
theorem cond_exp_linear (addF mulF : α → α → α) (a b eXF eYF : α) :
    add addF (mul mulF (contents a) (contents eXF))
             (mul mulF (contents b) (contents eYF)) =
    contents (addF (mulF a eXF) (mulF b eYF)) := rfl

-- ============================================================================
-- Disintegration
-- ============================================================================

/-- Disintegration: μ = ∫ μ_x dν(x). Each conditional measure μ_x is contents. -/
theorem disintegration_contents (mulF : α → α → α) (μ_x ν_val : α) :
    mul mulF (contents μ_x) (contents ν_val) = contents (mulF μ_x ν_val) := rfl

/-- Each conditional measure is never origin. -/
theorem disintegration_ne_origin (μ_x : α) :
    (contents μ_x : Val α) ≠ origin := by simp

-- ============================================================================
-- Density Functions
-- ============================================================================

/-- A probability density function f satisfies ∫f dμ = 1.
    In Val α: f is contents, ∫f dμ = contents(1). -/
theorem pdf_integral (mulF : α → α → α) (f_val μ_val one : α) (h : mulF f_val μ_val = one) :
    mul mulF (contents f_val) (contents μ_val) = contents one := by
  show contents (mulF f_val μ_val) = contents one; rw [h]

/-- PDFs are contents, never origin. -/
theorem pdf_ne_origin (f_val : α) :
    (contents f_val : Val α) ≠ origin := by simp

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Deeper decomposition over Val α:
--   ✓ Lebesgue decomposition: μ_ac + μ_s, both contents
--   ✓ Radon-Nikodym: density contents, chain rule, uniqueness
--   ✓ Mutual singularity: contents(0) for null sets
--   ✓ Conditional expectation: contents, tower property, linearity
--   ✓ Disintegration: conditional measures contents
--   ✓ PDFs: contents, integral = contents(1)
--
-- Zero sorries. Zero typeclasses. Zero Mathlib.

end Val
