/-
Extracted from LinearAlgebra/CrossProduct.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

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

The scope `Matrix` gives the following notation:

* `⨯₃` for the cross product

## Tags

cross product
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
