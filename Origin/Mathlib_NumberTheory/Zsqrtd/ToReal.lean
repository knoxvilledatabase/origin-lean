/-
Extracted from NumberTheory/Zsqrtd/ToReal.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# Image of `Zsqrtd` in `ℝ`

This file defines `Zsqrtd.toReal` and related lemmas.
It is in a separate file to avoid pulling in all of `Data.Real` into `Data.Zsqrtd`.
-/

namespace Zsqrtd

@[simps!]
noncomputable def toReal {d : ℤ} (h : 0 ≤ d) : ℤ√d →+* ℝ :=
  lift ⟨√↑d, Real.mul_self_sqrt (Int.cast_nonneg.mpr h)⟩

theorem toReal_injective {d : ℤ} (h0d : 0 ≤ d) (hd : ∀ n : ℤ, d ≠ n * n) :
    Function.Injective (toReal h0d) :=
  lift_injective _ hd

end Zsqrtd
