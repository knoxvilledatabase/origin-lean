/-
Extracted from Analysis/SpecialFunctions/Gamma/Deligne.lean
Genuine: 3 of 8 | Dissolved: 3 | Infrastructure: 2
-/
import Origin.Core

/-!
# Deligne's archimedean Gamma-factors

In the theory of L-series one frequently encounters the following functions (of a complex variable
`s`) introduced in Deligne's landmark paper *Valeurs de fonctions L et périodes d'intégrales*:

$$ \Gamma_{\mathbb{R}}(s) = \pi ^ {-s / 2} \Gamma (s / 2) $$

and

$$ \Gamma_{\mathbb{C}}(s) = 2 (2 \pi) ^ {-s} \Gamma (s). $$

These are the factors that need to be included in the Dedekind zeta function of a number field
for each real, resp. complex, infinite place.

(Note that these are *not* the same as Mathlib's `Real.Gamma` vs. `Complex.Gamma`; Deligne's
functions both take a complex variable as input.)

This file defines these functions, and proves some elementary properties, including a reflection
formula which is an important input in functional equations of (un-completed) Dirichlet L-functions.
-/

open Filter Topology Asymptotics Real Set MeasureTheory

open Complex

namespace Complex

noncomputable def Gammaℝ (s : ℂ) := π ^ (-s / 2) * Gamma (s / 2)

noncomputable def Gammaℂ (s : ℂ) := 2 * (2 * π) ^ (-s) * Gamma s

-- DISSOLVED: Gammaℝ_add_two

-- DISSOLVED: Gammaℂ_add_one

-- DISSOLVED: Gammaℝ_ne_zero_of_re_pos

lemma Gammaℝ_eq_zero_iff {s : ℂ} : Gammaℝ s = 0 ↔ ∃ n : ℕ, s = -(2 * n) := by
  simp [Gammaℝ_def, Complex.Gamma_eq_zero_iff, pi_ne_zero, div_eq_iff (two_ne_zero' ℂ), mul_comm]
