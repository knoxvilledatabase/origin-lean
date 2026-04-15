/-
Extracted from Algebra/Group/Int/Units.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Units in the integers
-/

open Nat

namespace Int

/-! #### Units -/

variable {u v : ℤ}

lemma units_natAbs (u : ℤˣ) : natAbs u = 1 :=
  Units.ext_iff.1 <|
    Nat.units_eq_one
      ⟨natAbs u, natAbs ↑u⁻¹, by rw [← natAbs_mul, Units.mul_inv]; rfl, by
        rw [← natAbs_mul, Units.inv_mul]; rfl⟩
