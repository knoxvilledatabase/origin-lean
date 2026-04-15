/-
Extracted from Algebra/Algebra/Operations.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Multiplication and division of submodules of an algebra.

An interface for multiplication and division of sub-R-modules of an R-algebra A is developed.

## Main definitions

Let `R` be a commutative ring (or semiring) and let `A` be an `R`-algebra.

* `1 : Submodule R A`   : the R-submodule R of the R-algebra A
* `Mul (Submodule R A)` : multiplication of two sub-R-modules M and N of A is defined to be
                              the smallest submodule containing all the products `m * n`.
* `Div (Submodule R A)` : `I / J` is defined to be the submodule consisting of all `a : A` such
                              that `a • J ⊆ I`

It is proved that `Submodule R A` is a semiring, and also an algebra over `Set A`.

Additionally, in the `Pointwise` scope we promote `Submodule.pointwiseDistribMulAction` to a
`MulSemiringAction` as `Submodule.pointwiseMulSemiringAction`.

When `R` is not necessarily commutative, and `A` is merely an `R`-module with a ring structure
such that `IsScalarTower R A A` holds (equivalent to the data of a ring homomorphism `R →+* A`
by `ringHomEquivModuleIsScalarTower`), we can still define `1 : Submodule R A` and
`Mul (Submodule R A)`, but `1` is only a left identity, not necessarily a right one.

## Tags

multiplication of submodules, division of submodules, submodule semiring
-/

universe uι u v

open Algebra Set MulOpposite

open Pointwise

namespace SubMulAction

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]

theorem algebraMap_mem (r : R) : algebraMap R A r ∈ (1 : SubMulAction R A) :=
  ⟨r, (algebraMap_eq_smul_one r).symm⟩

theorem mem_one' {x : A} : x ∈ (1 : SubMulAction R A) ↔ ∃ y, algebraMap R A y = x :=
  exists_congr fun r => by rw [algebraMap_eq_smul_one]

end SubMulAction

namespace Submodule

section Module

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

-- INSTANCE (free from Core): one

theorem one_eq_span : (1 : Submodule R A) = R ∙ 1 :=
  (LinearMap.span_singleton_eq_range _ _ _).symm

theorem le_one_toAddSubmonoid : 1 ≤ (1 : Submodule R A).toAddSubmonoid := by
  rintro x ⟨n, rfl⟩
  exact ⟨n, show (n : R) • (1 : A) = n by rw [Nat.cast_smul_eq_nsmul, nsmul_one]⟩
