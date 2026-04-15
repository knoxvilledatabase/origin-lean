/-
Extracted from Algebra/Ring/Action/Field.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# Group action on fields
-/

variable {M} [Monoid M] {F} [DivisionRing F]

@[simp]
theorem smul_inv'' [MulSemiringAction M F] (x : M) (m : F) : x • m⁻¹ = (x • m)⁻¹ :=
  map_inv₀ (MulSemiringAction.toRingHom M F x) _
