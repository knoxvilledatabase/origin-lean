/-
Extracted from Analysis/Complex/ValueDistribution/Proximity/Basic.lean
Genuine: 10 of 12 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Proximity Function of Value Distribution Theory

This file defines the "proximity function" attached to a meromorphic function defined on the complex
plane.  Also known as the `Nevanlinna Proximity Function`, this is one of the three main functions
used in Value Distribution Theory.

The proximity function is a logarithmically weighted measure quantifying how well a meromorphic
function `f` approximates the constant function `a` on the circle of radius `R` in the complex
plane.  The definition ensures that large values correspond to good approximation.

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.
-/

open Filter Metric Real Set

namespace ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E]
  {f g : ℂ → E} {a : WithTop E} {a₀ : E}

open Real

variable (f a) in

noncomputable def proximity : ℝ → ℝ := by
  by_cases h : a = ⊤
  · exact circleAverage (log⁺ ‖f ·‖) 0
  · exact circleAverage (log⁺ ‖f · - a.untop₀‖⁻¹) 0

lemma proximity_coe :
    proximity f a₀ = circleAverage (log⁺ ‖f · - a₀‖⁻¹) 0 := by
  simp [proximity]

lemma proximity_zero : proximity f 0 = circleAverage (log⁺ ‖f ·‖⁻¹) 0 := by
  simp [proximity]

lemma proximity_zero_of_complexValued {f : ℂ → ℂ} :
    proximity f 0 = circleAverage (log⁺ ‖f⁻¹ ·‖) 0 := by
  simp [proximity]

lemma proximity_top : proximity f ⊤ = circleAverage (log⁺ ‖f ·‖) 0 := by
  simp [proximity]

/-!
## Elementary Properties of the Proximity Function
-/

-- DISSOLVED: proximity_congr_codiscreteWithin

-- DISSOLVED: proximity_congr_codiscrete

lemma proximity_coe_eq_proximity_sub_const_zero :
    proximity f a₀ = proximity (f - fun _ ↦ a₀) 0 := by
  simp [proximity]

theorem proximity_inv {f : ℂ → ℂ} : proximity f⁻¹ ⊤ = proximity f 0 := by
  simp [proximity_zero, proximity_top]

theorem proximity_sub_proximity_inv_eq_circleAverage {f : ℂ → ℂ} (h₁f : Meromorphic f) :
    proximity f ⊤ - proximity f⁻¹ ⊤ = circleAverage (log ‖f ·‖) 0 := by
  ext R
  simp only [proximity, ↓reduceDIte, Pi.inv_apply, norm_inv, Pi.sub_apply]
  rw [← circleAverage_sub]
  · simp_rw [← posLog_sub_posLog_inv, Pi.sub_def]
  · apply h₁f.meromorphicOn.circleIntegrable_posLog_norm
  · simp_rw [← norm_inv]
    apply h₁f.inv.meromorphicOn.circleIntegrable_posLog_norm

theorem proximity_even : (proximity f a).Even := by
  intro r
  by_cases h : a = ⊤ <;> simp [proximity, h]

theorem proximity_nonneg {a : WithTop E} :
    0 ≤ proximity f a := by
  by_cases h : a = ⊤ <;>
  · intro r
    simpa [proximity, h] using circleAverage_nonneg_of_nonneg (fun x _ ↦ posLog_nonneg)
