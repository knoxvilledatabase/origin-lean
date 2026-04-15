/-
Extracted from LinearAlgebra/BilinearForm/Hom.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Bilinear form and linear maps

This file describes the relation between bilinear forms and linear maps.

## TODO

A lot of this file is now redundant following the replacement of the dedicated `_root_.BilinForm`
structure with `LinearMap.BilinForm`, which is just an alias for `M →ₗ[R] M →ₗ[R] R`. For example
`LinearMap.BilinForm.toLinHom` is now just the identity map. This redundant code should be removed.

## Notation

Given any term `B` of type `BilinForm`, due to a coercion, can use
the notation `B x y` to refer to the function field, i.e. `B x y = B.bilin x y`.

In this file we use the following type variables:
- `M`, `M'`, ... are modules over the commutative semiring `R`,
- `M₁`, `M₁'`, ... are modules over the commutative ring `R₁`,
- `V`, ... is a vector space over the field `K`.

## References

* <https://en.wikipedia.org/wiki/Bilinear_form>

## Tags

Bilinear form,
-/

open LinearMap (BilinForm)

open LinearMap (BilinMap)

open Module

universe u v w

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R₁ : Type*} {M₁ : Type*} [CommRing R₁] [AddCommGroup M₁] [Module R₁ M₁]

variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]

variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁}

namespace LinearMap

namespace BilinForm

section ToLin'

def toLinHomAux₁ (A : BilinForm R M) (x : M) : M →ₗ[R] R := A x

variable (B)

theorem sum_left {α} (t : Finset α) (g : α → M) (w : M) :
    B (∑ i ∈ t, g i) w = ∑ i ∈ t, B (g i) w :=
  B.map_sum₂ t g w

variable (w : M)

theorem sum_right {α} (t : Finset α) (w : M) (g : α → M) :
    B w (∑ i ∈ t, g i) = ∑ i ∈ t, B w (g i) := map_sum _ _ _

theorem sum_apply {α} (t : Finset α) (B : α → BilinForm R M) (v w : M) :
    (∑ i ∈ t, B i) v w = ∑ i ∈ t, B i v w := by
  simp only [coe_sum, Finset.sum_apply]

variable {B}

def toLinHomFlip : BilinForm R M →ₗ[R] M →ₗ[R] M →ₗ[R] R :=
  flipHom.toLinearMap

end ToLin'

end BilinForm

end LinearMap

namespace LinearMap

variable {R' : Type*} [CommSemiring R'] [Algebra R' R] [Module R' M] [IsScalarTower R' R M]
