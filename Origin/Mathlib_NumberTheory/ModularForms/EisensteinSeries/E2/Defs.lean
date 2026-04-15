/-
Extracted from NumberTheory/ModularForms/EisensteinSeries/E2/Defs.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Eisenstein Series E2

We define the Eisenstein series `E2` of weight `2` and level `1` as a limit of partial sums
over non-symmetric intervals.

-/

open UpperHalfPlane hiding I

open ModularForm EisensteinSeries Matrix.SpecialLinearGroup Filter Complex MatrixGroups

  SummationFilter Real

namespace EisensteinSeries

def e2Summand (m : ℤ) (z : ℍ) : ℂ := ∑' n, eisSummand 2 ![m, n] z

lemma e2Summand_summable (m : ℤ) (z : ℍ) : Summable (fun n ↦ eisSummand 2 ![m, n] z) := by
  apply (linear_right_summable z m (k := 2) (by grind)).congr
  simp [eisSummand]
