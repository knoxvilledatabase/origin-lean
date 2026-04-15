/-
Extracted from LinearAlgebra/Quotient/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Quotients by submodules

* If `p` is a submodule of `M`, `M ⧸ p` is the quotient of `M` with respect to `p`:
  that is, elements of `M` are identified if their difference is in `p`. This is itself a module.

## Main definitions

* `Submodule.Quotient.restrictScalarsEquiv`: The quotient of `P` as an `S`-submodule is the same
  as the quotient of `P` as an `R`-submodule,
* `Submodule.liftQ`: lift a map `M → M₂` to a map `M ⧸ p → M₂` if the kernel is contained in `p`
* `Submodule.mapQ`: lift a map `M → M₂` to a map `M ⧸ p → M₂ ⧸ q` if the image of `p` is contained
  in `q`

-/

assert_not_exists Cardinal

section Ring

namespace Submodule

variable {R M : Type*} {r : R} {x y : M} [Ring R] [AddCommGroup M] [Module R M]

variable (p p' p'' : Submodule R M)

open LinearMap QuotientAddGroup

namespace Quotient

section Module

variable (S : Type*)

def restrictScalarsEquiv [Ring S] [SMul S R] [Module S M] [IsScalarTower S R M]
    (P : Submodule R M) : (M ⧸ P.restrictScalars S) ≃ₗ[S] M ⧸ P :=
  { Quotient.congrRight fun _ _ => Iff.rfl with
    map_add' := fun x y => Quotient.inductionOn₂' x y fun _x' _y' => rfl
    map_smul' := fun _c x => Submodule.Quotient.induction_on _ x fun _x' => rfl }
