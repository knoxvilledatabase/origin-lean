/-
Extracted from Topology/Algebra/IsUniformGroup/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Uniform structure on topological groups

Given a topological group `G`, one can naturally build two uniform structures
(the "left" and "right" ones) on `G` inducing its topology.
This file defines typeclasses for groups equipped with either of these uniform structures, as well
as a separate typeclass for the (very common) case where the given uniform structure
coincides with **both** the left and right uniform structures.

## Main declarations

* `IsRightUniformGroup` and `IsRightUniformAddGroup`: Multiplicative and additive topological groups
  endowed with the associated right uniform structure. This means that two points `x` and `y`
  are close precisely when `y * x⁻¹` is close to `1` / `y + (-x)` close to `0`.
* `IsLeftUniformGroup` and `IsLeftUniformAddGroup`: Multiplicative and additive topological groups
  endowed with the associated left uniform structure. This means that two points `x` and `y`
  are close precisely when `x⁻¹ * y` is close to `1` / `(-x) + y` close to `0`.
* `IsUniformGroup` and `IsUniformAddGroup`: Multiplicative and additive uniform groups,
  i.e., groups with uniformly continuous `(*)` and `(⁻¹)` / `(+)` and `(-)`. This corresponds
  to the conjunction of the two conditions above, although this result is not in Mathlib yet.

## Main results

* `IsTopologicalAddGroup.rightUniformSpace` and `comm_topologicalAddGroup_is_uniform` can be used
  to construct a canonical uniformity for a topological additive group.

See `Mathlib/Topology/Algebra/IsUniformGroup/Basic.lean` for further results.

## Implementation Notes

Since the most frequent use case is `G` being a commutative additive groups, `Mathlib` originally
did essentially all the theory under the assumption `IsUniformGroup G`.
For this reason, you may find results stated under this assumption even though they may hold
under either `IsRightUniformGroup G` or `IsLeftUniformGroup G`.
-/

assert_not_exists Cauchy

noncomputable section

open Uniformity Topology Filter Pointwise

section LeftRight

open Filter Set

variable {G Gₗ Gᵣ Hₗ Hᵣ X : Type*}

class IsRightUniformAddGroup (G : Type*) [UniformSpace G] [AddGroup G] : Prop
    extends IsTopologicalAddGroup G where
  uniformity_eq :
    𝓤 G = comap (fun x : G × G ↦ x.2 + (-x.1)) (𝓝 0)
