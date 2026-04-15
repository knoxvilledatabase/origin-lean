/-
Extracted from LinearAlgebra/BilinearForm/Orthogonal.lean
Genuine: 7 of 10 | Dissolved: 1 | Infrastructure: 2
-/
import Origin.Core

/-!
# Bilinear form

This file defines orthogonal bilinear forms.

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

open Module

universe u v w

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R₁ : Type*} {M₁ : Type*} [CommRing R₁] [AddCommGroup M₁] [Module R₁ M₁]

variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]

variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁}

namespace LinearMap

namespace BilinForm

def IsOrtho (B : BilinForm R M) (x y : M) : Prop :=
  B x y = 0

theorem isOrtho_zero_left (x : M) : IsOrtho B (0 : M) x := LinearMap.isOrtho_zero_left B x

theorem isOrtho_zero_right (x : M) : IsOrtho B x (0 : M) :=
  zero_right x

-- DISSOLVED: ne_zero_of_not_isOrtho_self

theorem IsRefl.ortho_comm (H : B.IsRefl) {x y : M} : IsOrtho B x y ↔ IsOrtho B y x :=
  ⟨eq_zero H, eq_zero H⟩

theorem IsAlt.ortho_comm (H : B₁.IsAlt) {x y : M₁} : IsOrtho B₁ x y ↔ IsOrtho B₁ y x :=
  LinearMap.IsAlt.ortho_comm H

theorem IsSymm.ortho_comm (H : B.IsSymm) {x y : M} : IsOrtho B x y ↔ IsOrtho B y x :=
  LinearMap.IsSymm.ortho_comm (isSymm_iff.1 H)

def iIsOrtho {n : Type w} (B : BilinForm R M) (v : n → M) : Prop :=
  B.IsOrthoᵢ v

variable {R₄ M₄ : Type*} [CommRing R₄] [IsDomain R₄]

variable [AddCommGroup M₄] [Module R₄ M₄] {G : BilinForm R₄ M₄}
