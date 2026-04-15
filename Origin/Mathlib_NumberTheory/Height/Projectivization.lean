/-
Extracted from NumberTheory/Height/Projectivization.lean
Genuine: 6 of 11 | Dissolved: 5 | Infrastructure: 0
-/
import Origin.Core

/-!
# Heights of points in projective space

We define the multiplicative (`Projectivization.mulHeight`) and the logarithmic
(`Projectivization.logHeight`) height of a point in a (finite-dimensional) projective space
over a field that has a `Height.AdmissibleAbsValues` instance.

The height is defined to be the height of any representative tuple; it does not depend
on which representative is chosen.
-/

namespace Projectivization

open Height AdmissibleAbsValues Real

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*} [Finite ι]

-- DISSOLVED: mulHeight_aux

-- DISSOLVED: logHeight_aux

noncomputable def mulHeight (x : Projectivization K (ι → K)) : ℝ :=
  x.lift (fun r ↦ Height.mulHeight r.val) mulHeight_aux

noncomputable def logHeight (x : Projectivization K (ι → K)) : ℝ :=
  x.lift (fun r ↦ Height.logHeight r.val) logHeight_aux

-- DISSOLVED: mulHeight_mk

-- DISSOLVED: logHeight_mk

lemma logHeight_eq_log_mulHeight (x : Projectivization K (ι → K)) :
    logHeight x = log (mulHeight x) := by
  rw [← x.mk_rep, mulHeight_mk, logHeight_mk, Height.logHeight]

lemma one_le_mulHeight (x : Projectivization K (ι → K)) : 1 ≤ mulHeight x := by
  rw [← x.mk_rep, mulHeight_mk]
  exact Height.one_le_mulHeight _

lemma mulHeight_pos (x : Projectivization K (ι → K)) : 0 < mulHeight x :=
  zero_lt_one.trans_le <| one_le_mulHeight x

-- DISSOLVED: mulHeight_ne_zero

lemma logHeight_nonneg (x : Projectivization K (ι → K)) : 0 ≤ logHeight x := by
  rw [logHeight_eq_log_mulHeight]
  exact log_nonneg <| x.one_le_mulHeight

end Projectivization

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq Projectivization
