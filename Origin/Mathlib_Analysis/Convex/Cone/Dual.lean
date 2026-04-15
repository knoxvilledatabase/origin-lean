/-
Extracted from Analysis/Convex/Cone/Dual.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The topological dual of a cone and Farkas' lemma

Given a continuous bilinear pairing `p` between two `R`-modules `M` and `N` and a set `s` in `M`,
we define `ProperCone.dual p C` to be the proper cone in `N` consisting of all points `y` such that
`0 ≤ p x y` for all `x ∈ s`.

When the pairing is perfect, this gives us the algebraic dual of a cone.
See `Mathlib/Geometry/Convex/Cone/Dual.lean` for that case.
When the pairing is continuous and perfect (as a continuous pairing), this gives us the topological
dual instead. This is developed here.

We prove Farkas' lemma, which says that a proper cone `C` in a locally convex topological real
vector space `E` and a point `x₀` not in `C` can be separated by a hyperplane. This is a geometric
interpretation of the Hahn-Banach separation theorem.
As a corollary, we prove that the double dual of a proper cone is itself.

## Main statements

We prove the following theorems:
* `ProperCone.hyperplane_separation`, `ProperCone.hyperplane_separation_point`: Farkas lemma.
* `ProperCone.dual_dual_flip`, `ProperCone.dual_flip_dual`: The double dual of a proper cone.

## References

* https://en.wikipedia.org/wiki/Hyperplane_separation_theorem
* https://en.wikipedia.org/wiki/Farkas%27_lemma#Geometric_interpretation
-/

assert_not_exists InnerProductSpace

open Set LinearMap Pointwise

namespace PointedCone

variable {R M N : Type*} [CommRing R] [PartialOrder R] [TopologicalSpace R] [ClosedIciTopology R]
  [IsOrderedRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [TopologicalSpace N]
  {p : M →ₗ[R] N →ₗ[R] R} {s : Set M}

lemma isClosed_dual (hp : ∀ x, Continuous (p x)) : IsClosed (dual p s : Set N) := by
  rw [← s.biUnion_of_singleton]
  simp_rw [dual_iUnion, Submodule.coe_iInf, dual_singleton]
  exact isClosed_biInter fun x hx ↦ isClosed_Ici.preimage <| hp _

end PointedCone

namespace ProperCone

variable {R M N : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] [TopologicalSpace R]
  [ClosedIciTopology R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N]
  {p : M →ₗ[R] N →ₗ[R] R} [p.IsContPerfPair] {s t : Set M} {y : N}

variable (p s) in

def dual (s : Set M) : ProperCone R N where
  toSubmodule := PointedCone.dual p s
  isClosed' := PointedCone.isClosed_dual fun _ ↦ p.continuous_of_isContPerfPair
