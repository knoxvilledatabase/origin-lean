/-
Extracted from LinearAlgebra/ExteriorAlgebra/OfAlternating.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Extending an alternating map to the exterior algebra

## Main definitions

* `ExteriorAlgebra.liftAlternating`: construct a linear map out of the exterior algebra
  given alternating maps (corresponding to maps out of the exterior powers).
* `ExteriorAlgebra.liftAlternatingEquiv`: the above as a linear equivalence

## Main results

* `ExteriorAlgebra.lhom_ext`: linear maps from the exterior algebra agree if they agree on the
  exterior powers.

-/

variable {R M N N' : Type*}

variable [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup N']

variable [Module R M] [Module R N] [Module R N']

-- INSTANCE (free from Core): AlternatingMap.instModuleAddCommGroup

namespace ExteriorAlgebra

open CliffordAlgebra hiding ι

def liftAlternating : (∀ i, M [⋀^Fin i]→ₗ[R] N) →ₗ[R] ExteriorAlgebra R M →ₗ[R] N := by
  suffices
    (∀ i, M [⋀^Fin i]→ₗ[R] N) →ₗ[R]
      ExteriorAlgebra R M →ₗ[R] ∀ i, M [⋀^Fin i]→ₗ[R] N by
    refine LinearMap.compr₂ this ?_
    refine (LinearEquiv.toLinearMap ?_).comp (LinearMap.proj 0)
    exact AlternatingMap.constLinearEquivOfIsEmpty.symm
  refine CliffordAlgebra.foldl _ ?_ ?_
  · refine
      LinearMap.mk₂ R (fun m f i => (f i.succ).curryLeft m) (fun m₁ m₂ f => ?_) (fun c m f => ?_)
        (fun m f₁ f₂ => ?_) fun c m f => ?_
    all_goals
      ext i : 1
      simp only [map_smul, map_add, Pi.add_apply, Pi.smul_apply, AlternatingMap.curryLeft_add,
        AlternatingMap.curryLeft_smul, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  · -- when applied twice with the same `m`, this recursive step produces 0
    intro m x
    ext
    simp
