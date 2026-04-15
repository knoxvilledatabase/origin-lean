/-
Extracted from Analysis/CStarAlgebra/CompletelyPositiveMap.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Completely positive maps

A linear map `φ : A₁ →ₗ[ℂ] A₂` (where `A₁` and `A₂` are C⋆-algebras) is called
*completely positive (CP)* if `CStarMatrix.map (Fin k) (Fin k) φ` (i.e. applying `φ` to all
entries of a k × k matrix) is also positive for every `k : ℕ`.

This file defines completely positive maps and develops their basic API.

## Main results

+ `NonUnitalStarAlgHomClass.instCompletelyPositiveMapClass`: Non-unital star algebra
  homomorphisms are completely positive.

## Notation

+ `A₁ →CP A₂` denotes the type of CP maps from `A₁` to `A₂`. This notation is scoped to
  `CStarAlgebra`.

## Implementation notes

The morphism class `CompletelyPositiveMapClass` is designed to be part of the order hierarchy,
and only includes the order property; linearity is not mentioned at all. It is therefore meant
to be used in conjunction with `LinearMapClass`. This is meant to avoid mixing order and algebra
as much as possible.
-/

open scoped CStarAlgebra

structure CompletelyPositiveMap (A₁ : Type*) (A₂ : Type*) [NonUnitalCStarAlgebra A₁]
    [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
    [StarOrderedRing A₂] extends A₁ →ₗ[ℂ] A₂ where
  map_cstarMatrix_nonneg' (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 ≤ M) :
      0 ≤ M.map toLinearMap

class CompletelyPositiveMapClass (F : Type*) (A₁ : Type*) (A₂ : Type*)
    [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
    [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂] where
  map_cstarMatrix_nonneg' (φ : F) (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 ≤ M) :
    0 ≤ M.map φ

scoped[CStarAlgebra] notation:25 A₁ " →CP " A₂:0 => CompletelyPositiveMap A₁ A₂

namespace CompletelyPositiveMapClass

variable {F A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁]
  [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
  [StarOrderedRing A₂] [FunLike F A₁ A₂] [LinearMapClass F ℂ A₁ A₂]
