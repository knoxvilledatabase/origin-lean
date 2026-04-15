/-
Extracted from LinearAlgebra/RootSystem/Basic.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Root data and root systems

This file contains basic results for root systems and root data.

## Main definitions / results:

* `RootPairing.ext`: In characteristic zero if there is no torsion, the correspondence between
  roots and coroots is unique.
* `RootSystem.ext`: In characteristic zero if there is no torsion, a root system is determined
  entirely by its roots.
* `RootPairing.mk'`: In characteristic zero if there is no torsion, to check that two finite
  families of roots and coroots form a root pairing, it is sufficient to check that they are
  stable under reflections.
* `RootSystem.mk'`: In characteristic zero if there is no torsion, to check that a finite family of
  roots form a root system, we do not need to check that the coroots are stable under reflections
  since this follows from the corresponding property for the roots.

-/

open Set Function

open Module hiding reflection

open Submodule (span)

open AddSubgroup (zmultiples)

noncomputable section

variable {ι R M N : Type*}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

section reflectionPerm

variable (p : M →ₗ[R] N →ₗ[R] R) (root : ι ↪ M) (coroot : ι ↪ N) (i j : ι)
  (h : ∀ i, MapsTo (preReflection (root i) (p.flip (coroot i)))
    (range root) (range root))

include h

set_option backward.privateInPublic true in

variable (hp : ∀ i, p (root i) (coroot i) = 2)

include hp

set_option backward.privateInPublic true in

private theorem choose_choose_eq_of_mapsTo :
    (exist_eq_reflection_of_mapsTo p root coroot i
      (exist_eq_reflection_of_mapsTo p root coroot i j h).choose h).choose = j := by
  refine root.injective ?_
  rw [(exist_eq_reflection_of_mapsTo p root coroot i _ h).choose_spec,
    (exist_eq_reflection_of_mapsTo p root coroot i j h).choose_spec]
  apply involutive_preReflection (x := root i) (hp i)

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in
