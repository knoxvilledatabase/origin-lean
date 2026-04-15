/-
Extracted from LinearAlgebra/SpecialLinearGroup.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The special linear group of a module

If `R` is a commutative ring and `V` is an `R`-module,
we define `SpecialLinearGroup R V` as the subtype of
linear equivalences `V ≃ₗ[R] V` with determinant 1.
When `V` doesn't have a finite basis, the determinant is defined to be 1
and the definition gives `V ≃ₗ[R] V`.
The interest of this definition is that `SpecialLinearGroup R V`
has a group structure. (Starting from linear maps wouldn't have worked.)

The file is constructed parallel to the one defining `Matrix.SpecialLinearGroup`.

We provide `SpecialLinearGroup.toLinearEquiv`: the canonical map
from `SpecialLinearGroup R V` to `V ≃ₗ[R] V`, as a monoid hom.

When `V` is free and finite over `R`, we define
* `SpecialLinearGroup.dualMap`
* `SpecialLinearGroup.baseChange`

We define `Matrix.SpecialLinearGroup.toLin'_equiv`: the multiplicative equivalence
from `Matrix.SpecialLinearGroup n R` to `SpecialLinearGroup R (n → R)`
and its variant
`Matrix.SpecialLinearGroup.toLin_equiv`,
from `Matrix.SpecialLinearGroup n R` to `SpecialLinearGroup R V`,
associated with a finite basis of `V`.

-/

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

variable (R V) in

abbrev SpecialLinearGroup := { u : V ≃ₗ[R] V // u.det = 1 }

namespace SpecialLinearGroup

theorem det_eq_one (u : SpecialLinearGroup R V) :
    LinearMap.det (u : V →ₗ[R] V) = 1 := by
  simp [← LinearEquiv.coe_det, u.prop]

-- INSTANCE (free from Core): :

theorem ext_iff (u v : SpecialLinearGroup R V) : u = v ↔ ∀ x : V, u x = v x := by
  simp only [← Subtype.coe_inj, LinearEquiv.ext_iff]
