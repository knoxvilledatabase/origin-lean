/-
Extracted from Topology/Algebra/AffineSubspace.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Topology of affine subspaces.

This file defines the embedding map from an affine subspace to the ambient space as a continuous
affine map.

## Main definitions

* `AffineSubspace.subtypeA` is `AffineSubspace.subtype` as a `ContinuousAffineMap`.

-/

namespace AffineSubspace

variable {R V P : Type*} [Ring R] [AddCommGroup V] [Module R V] [TopologicalSpace P]
  [AddTorsor V P]

def subtypeA (s : AffineSubspace R P) [Nonempty s] : s →ᴬ[R] P where
  toAffineMap := s.subtype
  cont := continuous_subtype_val
