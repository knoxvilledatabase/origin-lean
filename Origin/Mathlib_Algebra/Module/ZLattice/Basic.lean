/-
Extracted from Algebra/Module/ZLattice/Basic.lean
Genuine: 3 of 4 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# ℤ-lattices

Let `E` be a finite-dimensional vector space over a `NormedLinearOrderedField` `K` with a solid
norm that is also a `FloorRing`, e.g. `ℝ`. A (full) `ℤ`-lattice `L` of `E` is a discrete
subgroup of `E` such that `L` spans `E` over `K`.

A `ℤ`-lattice `L` can be defined in two ways:
* For `b` a basis of `E`, then `L = Submodule.span ℤ (Set.range b)` is a ℤ-lattice of `E`
* As a `ℤ-submodule` of `E` with the additional properties:
  * `DiscreteTopology L`, that is `L` is discrete
  * `Submodule.span ℝ (L : Set E) = ⊤`, that is `L` spans `E` over `K`.

Results about the first point of view are in the `ZSpan` namespace and results about the second
point of view are in the `ZLattice` namespace.

## Main results and definitions

* `ZSpan.isAddFundamentalDomain`: for a ℤ-lattice `Submodule.span ℤ (Set.range b)`, proves that
  the set defined by `ZSpan.fundamentalDomain` is a fundamental domain.
* `ZLattice.module_free`: a `ℤ`-submodule of `E` that is discrete and spans `E` over `K` is a free
  `ℤ`-module
* `ZLattice.rank`: a `ℤ`-submodule of `E` that is discrete and spans `E` over `K` is free
  of `ℤ`-rank equal to the `K`-rank of `E`
* `ZLattice.comap`: for `e : E → F` a linear map and `L : Submodule ℤ E`, define the pullback of
  `L` by `e`. If `L` is a `IsZLattice` and `e` is a continuous linear equiv, then it is also a
  `IsZLattice`, see `instIsZLatticeComap`.

## Note

There is also `Submodule.IsLattice` which has slightly different applications. There no
topology is needed and the discrete condition is replaced by finitely generated.

## Implementation Notes

A `ZLattice` could be defined either as a `AddSubgroup E` or a `Submodule ℤ E`. However, the module
aspect appears to be the more useful one (especially in computations involving basis) and is also
consistent with the `ZSpan` construction of `ℤ`-lattices.

-/

noncomputable section

namespace ZSpan

open MeasureTheory MeasurableSet Module Submodule Bornology

variable {E ι : Type*}

section NormedLatticeField

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

theorem span_top : span K (span ℤ (Set.range b) : Set E) = ⊤ := by simp [span_span_of_tower]

theorem map {F : Type*} [AddCommGroup F] [Module K F] (f : E ≃ₗ[K] F) :
    Submodule.map (f.restrictScalars ℤ : E →ₗ[ℤ] F) (span ℤ (Set.range b)) =
      span ℤ (Set.range (b.map f)) := by
  simp_rw [Submodule.map_span, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply,
    Basis.coe_map, Set.range_comp]

open scoped Pointwise in

-- DISSOLVED: smul

variable [LinearOrder K]

def fundamentalDomain : Set E := {m | ∀ i, b.repr m i ∈ Set.Ico (0 : K) 1}
