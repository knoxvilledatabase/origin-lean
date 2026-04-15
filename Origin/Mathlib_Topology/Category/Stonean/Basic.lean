/-
Extracted from Topology/Category/Stonean/Basic.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Extremally disconnected sets

This file develops some of the basic theory of extremally disconnected compact Hausdorff spaces.

## Overview

This file defines the type `Stonean` of all extremally (note: not "extremely"!)
disconnected compact Hausdorff spaces, gives it the structure of a large category,
and proves some basic observations about this category and various functors from it.

The Lean implementation: a term of type `Stonean` is a pair, considering of
a term of type `CompHaus` (i.e. a compact Hausdorff topological space) plus
a proof that the space is extremally disconnected.
This is equivalent to the assertion that the term is projective in `CompHaus`,
in the sense of category theory (i.e., such that morphisms out of the object
can be lifted along epimorphisms).

## Main definitions

* `Stonean` : the category of extremally disconnected compact Hausdorff spaces.
* `Stonean.toCompHaus` : the forgetful functor `Stonean ⥤ CompHaus` from Stonean
  spaces to compact Hausdorff spaces
* `Stonean.toProfinite` : the functor from Stonean spaces to profinite spaces.

## Implementation

The category `Stonean` is defined using the structure `CompHausLike`. See the file
`CompHausLike.Basic` for more information.

-/

universe u

open CategoryTheory

open scoped Topology

abbrev Stonean := CompHausLike (fun X ↦ ExtremallyDisconnected X)

namespace CompHaus

-- INSTANCE (free from Core): (X
