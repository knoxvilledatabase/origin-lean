/-
Extracted from Analysis/CStarAlgebra/Unitary/Maps.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Unitary maps in C⋆-algebras

This file defines some basic maps by unitaries in C⋆-algebras. -/

namespace Unitary

variable {R A : Type*} [NormedRing A] [StarRing A] [CStarRing A] [Ring R] [Module R A]

section mulLeft

variable [SMulCommClass R A A]

variable (R A) in

noncomputable def mulLeft : unitary A →* A ≃ₗᵢ[R] A where
  toFun u :=
    { __ := (toUnits u).mulLeftLinearEquiv R A
      norm_map' _ := CStarRing.norm_coe_unitary_mul _ _ }
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

variable (R) in
