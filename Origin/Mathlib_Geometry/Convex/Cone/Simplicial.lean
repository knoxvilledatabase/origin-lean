/-
Extracted from Geometry/Convex/Cone/Simplicial.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Simplicial cones

A **simplicial cone** is a pointed convex cone that equals the conic hull of a finite linearly
independent set of vectors. We do not require that the generators span the ambient module.
However, when the cone is also generating, its generators linearly span the module.

## Main definitions

* `PointedCone.IsSimplicial`: A pointed cone is simplicial if it equals the conic hull of a finite
  linearly independent set.

## Results

* `PointedCone.IsSimplicial.span`: The conic hull of a linearly independent finite set is
  simplicial.

## References

* [Aubrun et al. *Entangleability of cones*][aubrunEntangleabilityCones2021]
-/

variable {R M : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

variable [AddCommMonoid M] [Module R M]

variable (C : PointedCone R M)

namespace PointedCone

def IsSimplicial : Prop :=
  ∃ s : Set M, s.Finite ∧ LinearIndepOn R id s ∧ hull R s = C

namespace IsSimplicial

protected theorem hull {s : Set M} (hs : s.Finite) (hli : LinearIndepOn R id s) :
    (PointedCone.hull R s).IsSimplicial := ⟨s, hs, hli, rfl⟩

end IsSimplicial

end PointedCone
