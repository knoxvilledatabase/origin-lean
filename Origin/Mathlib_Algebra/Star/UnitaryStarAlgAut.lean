/-
Extracted from Algebra/Star/UnitaryStarAlgAut.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The ⋆-algebra automorphism given by a unitary element

This file defines the ⋆-algebra automorphism on `R` given by a unitary `u`,
which is `Unitary.conjStarAlgAut S R u`, defined to be `x ↦ u * x * star u`.
-/

namespace Unitary

variable {S R : Type*} [Semiring R] [StarMul R]
  [SMul S R] [IsScalarTower S R R] [SMulCommClass S R R]

variable (S R) in

def conjStarAlgAut : unitary R →* (R ≃⋆ₐ[S] R) where
  toFun u :=
  { toRingEquiv := MulSemiringAction.toRingEquiv _ R (ConjAct.toConjAct <| toUnits u)
    map_smul' _ _ := smul_comm _ _ _ |>.symm
    map_star' _ := by
      dsimp [ConjAct.units_smul_def]
      simp [mul_assoc, ← Unitary.star_eq_inv] }
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_smul]
