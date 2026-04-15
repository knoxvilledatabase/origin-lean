/-
Extracted from Geometry/Convex/Cone/Dual.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The algebraic dual of a cone

Given a bilinear pairing `p` between two `R`-modules `M` and `N` and a set `s` in `M`, we define
`PointedCone.dual p s` to be the pointed cone in `N` consisting of all points `y` such that
`0 ≤ p x y` for all `x ∈ s`.

When the pairing is perfect, this gives us the algebraic dual of a cone. This is developed here.
When the pairing is continuous and perfect (as a continuous pairing), this gives us the topological
dual instead. See `Mathlib/Analysis/Convex/Cone/Dual.lean` for that case.

## Implementation notes

We do not provide a `ConvexCone`-valued version of `PointedCone.dual` since the dual cone of any set
always contains `0`, i.e. is a pointed cone.
Furthermore, the strict version `{y | ∀ x ∈ s, 0 < p x y}` is a candidate to the name
`ConvexCone.dual`.

-/

assert_not_exists TopologicalSpace Real Cardinal

open Function LinearMap Pointwise Set

namespace PointedCone

section CommSemiring

variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable {N : Type*} [AddCommMonoid N] [Module R N]

variable {p : M →ₗ[R] N →ₗ[R] R} {s t : Set M} {y : N}

local notation3 "R≥0" => {c : R // 0 ≤ c}

set_option backward.isDefEq.respectTransparency false in

variable (p) in

def dual (s : Set M) : PointedCone R N where
  carrier := {y | ∀ ⦃x⦄, x ∈ s → 0 ≤ p x y}
  zero_mem' := by simp
  add_mem' {u v} hu hv x hx := by rw [map_add]; exact add_nonneg (hu hx) (hv hx)
  smul_mem' c y hy x hx := by rw [← Nonneg.coe_smul, map_smul]; exact mul_nonneg c.2 (hy hx)
