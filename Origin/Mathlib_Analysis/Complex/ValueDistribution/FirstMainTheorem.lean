/-
Extracted from Analysis/Complex/ValueDistribution/FirstMainTheorem.lean
Genuine: 4 of 7 | Dissolved: 1 | Infrastructure: 2
-/
import Origin.Core

/-!
# The First Main Theorem of Value Distribution Theory

The First Main Theorem of Value Distribution Theory is a two-part statement, establishing invariance
of the characteristic function `characteristic f ⊤` under modifications of `f`.

- If `f` is meromorphic on the complex plane, then the characteristic functions for the value `⊤` of
  the function `f` and `f⁻¹` agree up to a constant, see Proposition 2.1 on p. 168 of [Lang,
  *Introduction to Complex Hyperbolic Spaces*][MR886677].

- If `f` is meromorphic on the complex plane, then the characteristic functions for the value `⊤` of
  the function `f` and `f - const` agree up to a constant, see Proposition 2.2 on p. 168 of [Lang,
  *Introduction to Complex Hyperbolic Spaces*][MR886677]

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.
-/

namespace ValueDistribution

open Asymptotics Filter Function.locallyFinsuppWithin MeromorphicAt MeromorphicOn Metric Real

section FirstPart

variable {f : ℂ → ℂ} {R : ℝ}

/-!
## First Part of the First Main Theorem
-/

lemma characteristic_sub_characteristic_inv (h : Meromorphic f) :
    characteristic f ⊤ - characteristic f⁻¹ ⊤ =
      circleAverage (log ‖f ·‖) 0 - (divisor f Set.univ).logCounting := by
  calc characteristic f ⊤ - characteristic f⁻¹ ⊤
  _ = proximity f ⊤ - proximity f⁻¹ ⊤ - (logCounting f⁻¹ ⊤ - logCounting f ⊤) := by
    unfold characteristic
    ring
  _ = circleAverage (log ‖f ·‖) 0 - (logCounting f⁻¹ ⊤ - logCounting f ⊤) := by
    rw [proximity_sub_proximity_inv_eq_circleAverage h]
  _ = circleAverage (log ‖f ·‖) 0 - (logCounting f 0 - logCounting f ⊤) := by
    rw [logCounting_inv]
  _ = circleAverage (log ‖f ·‖) 0 - (divisor f Set.univ).logCounting := by
    rw [← ValueDistribution.log_counting_zero_sub_logCounting_top]

-- DISSOLVED: characteristic_sub_characteristic_inv_of_ne_zero

theorem characteristic_sub_characteristic_inv_le (hf : Meromorphic f) :
    |characteristic f ⊤ R - characteristic f⁻¹ ⊤ R|
      ≤ max |log ‖f 0‖| |log ‖meromorphicTrailingCoeffAt f 0‖| := by
  by_cases h : R = 0
  · simp [h, characteristic_sub_characteristic_inv_at_zero hf]
  · simp [characteristic_sub_characteristic_inv_of_ne_zero hf h]

theorem isBigO_characteristic_sub_characteristic_inv (h : Meromorphic f) :
    (characteristic f ⊤ - characteristic f⁻¹ ⊤) =O[atTop] (1 : ℝ → ℝ) :=
  isBigO_of_le' (c := max |log ‖f 0‖| |log ‖meromorphicTrailingCoeffAt f 0‖|) _
    (fun R ↦ by simpa using characteristic_sub_characteristic_inv_le h (R := R))

end FirstPart

section SecondPart

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {a₀ : E} {f : ℂ → E}

/-!
## Second Part of the First Main Theorem
-/

theorem isBigO_characteristic_sub_characteristic_shift (h : Meromorphic f) :
    (characteristic f ⊤ - characteristic (f · - a₀) ⊤) =O[atTop] (1 : ℝ → ℝ) :=
  isBigO_of_le' (c := log⁺ ‖a₀‖ + log 2) _
    (fun R ↦ by simpa using abs_characteristic_sub_characteristic_shift_le h)
