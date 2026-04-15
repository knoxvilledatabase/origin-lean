/-
Extracted from Topology/Compactification/OnePoint/Basic.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The one-point compactification

We construct the one-point compactification of an arbitrary topological space `X` and prove some
properties inherited from `X`.

## Main definitions

* `OnePoint`: the one-point compactification, we use coercion for the canonical embedding
  `X → OnePoint X`; when `X` is already compact, the compactification adds an isolated point
  to the space.
* `OnePoint.infty`: the extra point

## Main results

* The topological structure of `OnePoint X`
* The connectedness of `OnePoint X` for a noncompact, preconnected `X`
* `OnePoint X` is `T₀` for a T₀ space `X`
* `OnePoint X` is `T₁` for a T₁ space `X`
* `OnePoint X` is normal if `X` is a locally compact Hausdorff space

## Tags

one point compactification, Alexandroff compactification, compactness
-/

open Set Filter Topology

/-!
### Definition and basic properties

In this section we define `OnePoint X` to be the disjoint union of `X` and `∞`, implemented as
`Option X`. Then we restate some lemmas about `Option X` for `OnePoint X`.
-/

variable {X Y : Type*}

def OnePoint (X : Type*) :=
  Option X

-- INSTANCE (free from Core): [Repr

namespace OnePoint
