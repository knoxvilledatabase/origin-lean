/-
Extracted from NumberTheory/NumberField/InfiniteAdeleRing.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The infinite adele ring of a number field

This file contains the formalisation of the infinite adele ring of a number field as the
finite product of completions over its infinite places.

## Main definitions

- `NumberField.InfiniteAdeleRing` of a number field `K` is defined as the product of
  the completions of `K` over its infinite places.
- `NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace` is the ring isomorphism between
  the infinite adele ring of `K` and `ℝ ^ r₁ × ℂ ^ r₂`, where `(r₁, r₂)` is the signature of `K`.

## Main results
- `NumberField.InfiniteAdeleRing.locallyCompactSpace` : the infinite adele ring is a
  locally compact space.

## References
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
infinite adele ring, number field
-/

noncomputable section

namespace NumberField

open InfinitePlace AbsoluteValue.Completion InfinitePlace.Completion IsDedekindDomain

/-! ## The infinite adele ring

The infinite adele ring is the finite product of completions of a number field over its
infinite places. See `NumberField.InfinitePlace` for the definition of an infinite place and
`NumberField.InfinitePlace.Completion` for the associated completion.
-/

def InfiniteAdeleRing (K : Type*) [Field K] := (v : InfinitePlace K) → v.Completion

deriving CommRing, Inhabited, TopologicalSpace, IsTopologicalRing, Algebra K

namespace InfiniteAdeleRing

variable (K : Type*) [Field K]

-- INSTANCE (free from Core): [NumberField
