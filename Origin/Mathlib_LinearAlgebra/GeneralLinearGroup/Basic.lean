/-
Extracted from LinearAlgebra/GeneralLinearGroup/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The general linear group of linear maps

The general linear group is defined to be the group of invertible linear maps from `M` to itself.

See also `Matrix.GeneralLinearGroup`

## Main definitions

* `LinearMap.GeneralLinearGroup`

-/

variable (R M : Type*)

namespace LinearMap

variable [Semiring R] [AddCommMonoid M] [Module R M]

abbrev GeneralLinearGroup :=
  (M →ₗ[R] M)ˣ

namespace GeneralLinearGroup

variable {R M}

def toLinearEquiv (f : GeneralLinearGroup R M) : M ≃ₗ[R] M :=
  { f.val with
    invFun := f.inv.toFun
    left_inv := fun m ↦ show (f.inv * f.val) m = m by simp
    right_inv := fun m ↦ show (f.val * f.inv) m = m by simp }
