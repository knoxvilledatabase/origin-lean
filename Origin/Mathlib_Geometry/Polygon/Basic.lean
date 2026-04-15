/-
Extracted from Geometry/Polygon/Basic.lean
Genuine: 6 of 12 | Dissolved: 4 | Infrastructure: 2
-/
import Origin.Core

/-!
# Polygons

This file defines polygons in affine spaces.
For the special case `n = 3`, an interconversion is provided with `Affine.Triangle`.

## Main definitions

* `Polygon P n`: A polygon with `n` vertices in a type `P`.

-/

open Set

structure Polygon (P : Type*) (n : ℕ) where
  /-- The vertices of the polygon, indexed by `Fin n`. -/
  vertices : Fin n → P

namespace Polygon

variable {R V P : Type*} {n : ℕ}

-- INSTANCE (free from Core): :

def HasNondegenerateEdges (poly : Polygon P n) : Prop :=
  ∀ i : Fin n, poly i ≠ poly (finRotate n i)

-- DISSOLVED: HasNondegenerateEdges.two_le

variable [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P]

variable (R) in

def edgePath (poly : Polygon P n) (i : Fin n) : R →ᵃ[R] P :=
  AffineMap.lineMap (poly i) (poly (finRotate n i))

variable (R) in

def edgeSet [PartialOrder R] (poly : Polygon P n) (i : Fin n) : Set P :=
  affineSegment R (poly i) (poly (finRotate n i))

variable (R) in

variable (R) in

def boundary [PartialOrder R] (poly : Polygon P n) : Set P :=
  ⋃ i, poly.edgeSet R i

variable (R) in

-- DISSOLVED: HasNondegenerateVertices

-- DISSOLVED: HasNondegenerateVertices.hasNondegenerateEdges

-- DISSOLVED: HasNondegenerateVertices.three_le

end Polygon

/-! ### Interconversion with `Affine.Triangle` -/

namespace Affine.Triangle

variable {R V P : Type*}

variable [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P]

def toPolygon : Affine.Triangle R P ↪ Polygon P 3 where
  toFun t := ⟨t.points⟩
  inj' t₁ t₂ h := by
    apply Simplex.ext
    apply_fun Polygon.vertices at h
    simp_all
