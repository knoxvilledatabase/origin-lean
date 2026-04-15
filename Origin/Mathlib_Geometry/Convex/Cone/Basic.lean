/-
Extracted from Geometry/Convex/Cone/Basic.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Convex cones

In an `R`-module `M`, we define a convex cone as a set `s` such that `a • x + b • y ∈ s` whenever
`x, y ∈ s` and `a, b > 0`. We prove that convex cones form a `CompleteLattice`, and define their
images (`ConvexCone.map`) and preimages (`ConvexCone.comap`) under linear maps.

We define pointed, blunt, flat and salient cones, and prove the correspondence between
convex cones and ordered modules.

We define `Convex.toCone` to be the minimal cone that includes a given convex set.

## Main statements

In `Mathlib/Analysis/Convex/Cone/Extension.lean` we prove
the M. Riesz extension theorem and a form of the Hahn-Banach theorem.

In `Mathlib/Analysis/Convex/Cone/Dual.lean` we prove
a variant of the hyperplane separation theorem.

## Implementation notes

While `Convex R` is a predicate on sets, `ConvexCone R M` is a bundled convex cone.

## References

* https://en.wikipedia.org/wiki/Convex_cone
* [Stephen P. Boyd and Lieven Vandenberghe, *Convex Optimization*][boydVandenberghe2004]
* [Emo Welzl and Bernd Gärtner, *Cone Programming*][welzl_garter]
-/

assert_not_exists TopologicalSpace Real Cardinal

open Set LinearMap Pointwise

variable {𝕜 R G M N O : Type*}

/-! ### Definition of `ConvexCone` and basic properties -/

section Definitions

variable [Semiring R] [PartialOrder R]

variable (R M) in

structure ConvexCone [AddCommMonoid M] [SMul R M] where
  /-- The **carrier set** underlying this cone: the set of points contained in it -/
  carrier : Set M
  smul_mem' : ∀ ⦃c : R⦄, 0 < c → ∀ ⦃x : M⦄, x ∈ carrier → c • x ∈ carrier
  add_mem' : ∀ ⦃x⦄ (_ : x ∈ carrier) ⦃y⦄ (_ : y ∈ carrier), x + y ∈ carrier

end Definitions

namespace ConvexCone

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [AddCommMonoid M]

section SMul

variable [SMul R M] {C C₁ C₂ : ConvexCone R M} {s : Set M} {c : R} {x : M}

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :
