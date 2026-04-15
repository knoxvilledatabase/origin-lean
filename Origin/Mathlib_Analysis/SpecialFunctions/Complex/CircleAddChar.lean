/-
Extracted from Analysis/SpecialFunctions/Complex/CircleAddChar.lean
Genuine: 9 of 11 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Additive characters valued in the unit circle

This file defines additive characters, valued in the unit circle, from either
* the ring `ZMod N` for any non-zero natural `N`,
* the additive circle `ℝ / T ⬝ ℤ`, for any real `T`.

These results are separate from `Analysis.SpecialFunctions.Complex.Circle` in order to reduce
the imports of that file.
-/

open Complex Function

open scoped Real

noncomputable def AddCircle.toCircle_addChar {T : ℝ} : AddChar (AddCircle T) Circle where
  toFun := toCircle
  map_zero_eq_one' := toCircle_zero
  map_add_eq_mul' := toCircle_add

open AddCircle

namespace ZMod

/-!
### Additive characters valued in the complex circle
-/

open scoped Real

variable {N : ℕ} [NeZero N]

noncomputable def toCircle : AddChar (ZMod N) Circle :=
  toCircle_addChar.compAddMonoidHom toAddCircle

lemma toCircle_intCast (j : ℤ) :
    toCircle (j : ZMod N) = exp (2 * π * I * j / N) := by
  rw [toCircle, AddChar.compAddMonoidHom_apply, toCircle_addChar, AddChar.coe_mk,
    AddCircle.toCircle, toAddCircle_intCast, Function.Periodic.lift_coe, Circle.coe_exp]
  push_cast
  ring_nf

lemma toCircle_natCast (j : ℕ) :
    toCircle (j : ZMod N) = exp (2 * π * I * j / N) := by
  simpa using toCircle_intCast (N := N) j

lemma toCircle_apply (j : ZMod N) :
    toCircle j = exp (2 * π * I * j.val / N) := by
  rw [← toCircle_natCast, natCast_zmod_val]

lemma injective_toCircle : Injective (toCircle : ZMod N → Circle) :=
  (AddCircle.injective_toCircle one_ne_zero).comp (toAddCircle_injective N)

noncomputable def stdAddChar : AddChar (ZMod N) ℂ := Circle.coeHom.compAddChar toCircle

lemma stdAddChar_coe (j : ℤ) :
    stdAddChar (j : ZMod N) = exp (2 * π * I * j / N) := by simp [stdAddChar, toCircle_intCast]

lemma stdAddChar_apply (j : ZMod N) : stdAddChar j = ↑(toCircle j) := rfl

lemma injective_stdAddChar : Injective (stdAddChar : AddChar (ZMod N) ℂ) :=
  Subtype.coe_injective.comp injective_toCircle

-- DISSOLVED: isPrimitive_stdAddChar

end ZMod
