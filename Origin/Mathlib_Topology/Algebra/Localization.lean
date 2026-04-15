/-
Extracted from Topology/Algebra/Localization.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# Localization of topological rings

The topological localization of a topological commutative ring `R` at a submonoid `M` is the ring
`Localization M` endowed with the final ring topology of the natural homomorphism sending `x : R`
to the equivalence class of `(x, 1)` in the localization of `R` at an `M`.

## Main Results

- `Localization.ringTopology`: The localization of a topological commutative ring at a submonoid
  is a topological ring.

-/

variable {R : Type*} [CommRing R] [TopologicalSpace R] {M : Submonoid R}

def Localization.ringTopology : RingTopology (Localization M) :=
  RingTopology.coinduced (Localization.monoidOf M).toFun

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :
