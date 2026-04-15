/-
Extracted from Algebra/LieRinehartAlgebra/Defs.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lie-Rinehart algebras

This file defines Lie-Rinehart algebras and their morphisms. It also shows that the derivations of
a commutative algebra over a commutative Ring form such a Lie-Rinehart algebra.
Lie-Rinehart algebras appear in differential geometry as section spaces of Lie algebroids and
singular foliations. The typical Cartan calculus of differential geometry can be restated fully in
terms of the Chevalley-Eilenberg algebra of a Lie-Rinehart algebra.

## References

* [Rinehart, G. S., Differential forms on general commutative algebras. Zbl 0113.26204
  Trans. Am. Math. Soc. 108, 195-222 (1963).][rinehart_1963]

-/

class LieRinehartRing (A L : Type*) [CommRing A] [LieRing L]
    [Module A L] [LieRingModule L A] : Prop where
  lie_smul_eq_mul' (a b : A) (x : L) : ⁅a • x, b⁆ = a * ⁅x, b⁆
  leibniz_mul_right' (x : L) (a b : A) : ⁅x, a * b⁆ = a • ⁅x, b⁆ + ⁅x, a⁆ * b
  leibniz_smul_right' (x y : L) (a : A) : ⁅x, a • y⁆ = a • ⁅x, y⁆ + ⁅x, a⁆ • y

class LieRinehartAlgebra (R A L : Type*) [CommRing A] [LieRing L]
    [Module A L] [LieRingModule L A] [LieRinehartRing A L]
    [CommRing R] [Algebra R A] [LieAlgebra R L] : Prop extends
    IsScalarTower R A L, LieModule R L A

namespace LieRinehartAlgebra

variable {R A₁ L₁ A₂ L₂ A₃ L₃ : Type*} [CommRing R]
  [CommRing A₁] [LieRing L₁] [Module A₁ L₁] [LieRingModule L₁ A₁]
  [CommRing A₂] [LieRing L₂] [Module A₂ L₂] [LieRingModule L₂ A₂]
  [CommRing A₃] [LieRing L₃] [Module A₃ L₃] [LieRingModule L₃ A₃]
  [Algebra R A₁] [LieAlgebra R L₁] [Algebra R A₂] [LieAlgebra R L₂]
  [Algebra R A₃] [LieAlgebra R L₃]
  {σ₁₂ : A₁ →ₐ[R] A₂} {σ₂₃ : A₂ →ₐ[R] A₃}
