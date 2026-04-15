/-
Extracted from LinearAlgebra/BilinearForm/Properties.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bilinear form

This file defines various properties of bilinear forms, including reflexivity, symmetry,
alternativity, adjoint, and non-degeneracy.
For orthogonality, see `Mathlib/LinearAlgebra/BilinearForm/Orthogonal.lean`.

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

variable {M' : Type*} [AddCommMonoid M'] [Module R M']

variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁}

namespace LinearMap

namespace BilinForm

/-! ### Reflexivity, symmetry, and alternativity -/

def IsRefl (B : BilinForm R M) : Prop := LinearMap.IsRefl B

namespace IsRefl

theorem eq_zero (H : B.IsRefl) : ∀ {x y : M}, B x y = 0 → B y x = 0 := fun {x y} => H x y

protected theorem neg {B : BilinForm R₁ M₁} (hB : B.IsRefl) : (-B).IsRefl := fun x y =>
  neg_eq_zero.mpr ∘ hB x y ∘ neg_eq_zero.mp

protected theorem smul {α : Type*} [Semiring α] [IsDomain α] [Module α R] [SMulCommClass R α R]
    [IsTorsionFree α R] (a : α) {B : BilinForm R M} (hB : B.IsRefl) :
    (a • B).IsRefl := fun _ _ h =>
  (smul_eq_zero.mp h).elim (fun ha => smul_eq_zero_of_left ha _) fun hBz =>
    smul_eq_zero_of_right _ (hB _ _ hBz)

protected theorem groupSMul {α} [Group α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
    {B : BilinForm R M} (hB : B.IsRefl) : (a • B).IsRefl := fun x y =>
  (smul_eq_zero_iff_eq _).mpr ∘ hB x y ∘ (smul_eq_zero_iff_eq _).mp

end IsRefl
