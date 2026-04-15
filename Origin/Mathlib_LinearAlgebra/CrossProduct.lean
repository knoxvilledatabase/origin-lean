/-
Extracted from LinearAlgebra/CrossProduct.lean
Genuine: 13 of 15 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Lie.Basic

/-!
# Cross products

This module defines the cross product of vectors in $R^3$ for $R$ a commutative ring,
as a bilinear map.

## Main definitions

* `crossProduct` is the cross product of pairs of vectors in $R^3$.

## Main results

* `triple_product_eq_det`
* `cross_dot_cross`
* `jacobi_cross`

## Notation

The locale `Matrix` gives the following notation:

* `×₃` for the cross product

## Tags

crossproduct
-/

open Matrix

variable {R : Type*} [CommRing R]

def crossProduct : (Fin 3 → R) →ₗ[R] (Fin 3 → R) →ₗ[R] Fin 3 → R := by
  apply LinearMap.mk₂ R fun a b : Fin 3 → R =>
      ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]
  · intros
    simp_rw [vec3_add, Pi.add_apply]
    apply vec3_eq <;> ring
  · intros
    simp_rw [smul_vec3, Pi.smul_apply, smul_sub, smul_mul_assoc]
  · intros
    simp_rw [vec3_add, Pi.add_apply]
    apply vec3_eq <;> ring
  · intros
    simp_rw [smul_vec3, Pi.smul_apply, smul_sub, mul_smul_comm]

scoped[Matrix] infixl:74 " ×₃ " => crossProduct

theorem cross_apply (a b : Fin 3 → R) :
    a ×₃ b = ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0] := rfl

section ProductsProperties

@[simp]
theorem cross_anticomm (v w : Fin 3 → R) : -(v ×₃ w) = w ×₃ v := by
  simp [cross_apply, mul_comm]

alias neg_cross := cross_anticomm

@[simp]
theorem cross_anticomm' (v w : Fin 3 → R) : v ×₃ w + w ×₃ v = 0 := by
  rw [add_eq_zero_iff_eq_neg, cross_anticomm]

@[simp]
theorem cross_self (v : Fin 3 → R) : v ×₃ v = 0 := by
  simp [cross_apply, mul_comm]

@[simp 1100] -- Porting note: increase priority so that the LHS doesn't simplify
theorem dot_self_cross (v w : Fin 3 → R) : v ⬝ᵥ v ×₃ w = 0 := by
  rw [cross_apply, vec3_dotProduct]
  norm_num
  ring

@[simp 1100] -- Porting note: increase priority so that the LHS doesn't simplify
theorem dot_cross_self (v w : Fin 3 → R) : w ⬝ᵥ v ×₃ w = 0 := by
  rw [← cross_anticomm, Matrix.dotProduct_neg, dot_self_cross, neg_zero]

theorem triple_product_permutation (u v w : Fin 3 → R) : u ⬝ᵥ v ×₃ w = v ⬝ᵥ w ×₃ u := by
  simp_rw [cross_apply, vec3_dotProduct]
  norm_num
  ring

theorem triple_product_eq_det (u v w : Fin 3 → R) : u ⬝ᵥ v ×₃ w = Matrix.det ![u, v, w] := by
  rw [vec3_dotProduct, cross_apply, det_fin_three]
  norm_num
  ring

theorem cross_dot_cross (u v w x : Fin 3 → R) :
    u ×₃ v ⬝ᵥ w ×₃ x = u ⬝ᵥ w * v ⬝ᵥ x - u ⬝ᵥ x * v ⬝ᵥ w := by
  simp_rw [cross_apply, vec3_dotProduct]
  norm_num
  ring

end ProductsProperties

section LeibnizProperties

theorem leibniz_cross (u v w : Fin 3 → R) : u ×₃ (v ×₃ w) = u ×₃ v ×₃ w + v ×₃ (u ×₃ w) := by
  simp_rw [cross_apply, vec3_add]
  apply vec3_eq <;> norm_num <;> ring

def Cross.lieRing : LieRing (Fin 3 → R) :=
  { Pi.addCommGroup with
    bracket := fun u v => u ×₃ v
    add_lie := LinearMap.map_add₂ _
    lie_add := fun _ => LinearMap.map_add _
    lie_self := cross_self
    leibniz_lie := leibniz_cross }

attribute [local instance] Cross.lieRing

theorem cross_cross (u v w : Fin 3 → R) : u ×₃ v ×₃ w = u ×₃ (v ×₃ w) - v ×₃ (u ×₃ w) :=
  lie_lie u v w

theorem jacobi_cross (u v w : Fin 3 → R) : u ×₃ (v ×₃ w) + v ×₃ (w ×₃ u) + w ×₃ (u ×₃ v) = 0 :=
  lie_jacobi u v w

end LeibnizProperties

-- DISSOLVED: crossProduct_ne_zero_iff_linearIndependent
