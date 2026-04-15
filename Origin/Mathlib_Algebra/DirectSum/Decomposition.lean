/-
Extracted from Algebra/DirectSum/Decomposition.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Decompositions of additive monoids, groups, and modules into direct sums

## Main definitions

* `DirectSum.Decomposition ℳ`: A typeclass to provide a constructive decomposition from
  an additive monoid `M` into a family of additive submonoids `ℳ`
* `DirectSum.decompose ℳ`: The canonical equivalence provided by the above typeclass


## Main statements

* `DirectSum.Decomposition.isInternal`: The link to `DirectSum.IsInternal`.

## Implementation details

As we want to talk about different types of decomposition (additive monoids, modules, rings, ...),
we choose to avoid heavily bundling `DirectSum.decompose`, instead making copies for the
`AddEquiv`, `LinearEquiv`, etc. This means we have to repeat statements that follow from these
bundled homs, but means we don't have to repeat statements for different types of decomposition.
-/

variable {ι R M σ : Type*}

open DirectSum

namespace DirectSum

section AddCommMonoid

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

class Decomposition where
  decompose' : M → ⨁ i, ℳ i
  left_inv : Function.LeftInverse (DirectSum.coeAddMonoidHom ℳ) decompose'
  right_inv : Function.RightInverse (DirectSum.coeAddMonoidHom ℳ) decompose'

-- INSTANCE (free from Core): :

abbrev Decomposition.ofAddHom (decompose : M →+ ⨁ i, ℳ i)
    (h_left_inv : (DirectSum.coeAddMonoidHom ℳ).comp decompose = .id _)
    (h_right_inv : decompose.comp (DirectSum.coeAddMonoidHom ℳ) = .id _) : Decomposition ℳ where
  decompose' := decompose
  left_inv := DFunLike.congr_fun h_left_inv
  right_inv := DFunLike.congr_fun h_right_inv
