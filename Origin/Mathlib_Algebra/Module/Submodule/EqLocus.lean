/-
Extracted from Algebra/Module/Submodule/EqLocus.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The submodule of elements `x : M` such that `f x = g x`

## Main declarations

* `LinearMap.eqLocus`: the submodule of elements `x : M` such that `f x = g x`

## Tags
linear algebra, vector space, module

-/

variable {R : Type*} {R₂ : Type*}

variable {M : Type*} {M₂ : Type*}

/-! ### Properties of linear maps -/

namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring R₂]

variable [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R₂ M₂]

open Submodule

variable {τ₁₂ : R →+* R₂}

variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂]

def eqLocus (f g : F) : Submodule R M :=
  { (f : M →+ M₂).eqLocusM g with
    carrier := { x | f x = g x }
    smul_mem' := fun {r} {x} (hx : _ = _) => show _ = _ by
      -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` into `map_smulₛₗ _`
      simpa only [map_smulₛₗ _] using congr_arg (τ₁₂ r • ·) hx }
