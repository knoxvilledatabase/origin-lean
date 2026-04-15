/-
Extracted from Algebra/Homology/ShortComplex/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Short complexes

This file defines the category `ShortComplex C` of diagrams
`X₁ ⟶ X₂ ⟶ X₃` such that the composition is zero.

Note: This structure `ShortComplex C` was first introduced in
the Liquid Tensor Experiment.

-/

namespace CategoryTheory

open Category Limits

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]

variable (C) in

structure ShortComplex where
  /-- the first (left) object of a `ShortComplex` -/
  {X₁ : C}
  /-- the second (middle) object of a `ShortComplex` -/
  {X₂ : C}
  /-- the third (right) object of a `ShortComplex` -/
  {X₃ : C}
  /-- the first morphism of a `ShortComplex` -/
  f : X₁ ⟶ X₂
  /-- the second morphism of a `ShortComplex` -/
  g : X₂ ⟶ X₃
  /-- the composition of the two given morphisms is zero -/
  zero : f ≫ g = 0 := by cat_disch

namespace ShortComplex

attribute [reassoc (attr := simp)] ShortComplex.zero
