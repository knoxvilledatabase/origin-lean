/-
Extracted from CategoryTheory/FiberedCategory/Cocartesian.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Co-Cartesian morphisms

This file defines co-Cartesian resp. strongly co-Cartesian morphisms with respect to a functor
`p : 𝒳 ⥤ 𝒮`.

This file has been adapted from `Mathlib/CategoryTheory/FiberedCategory/Cartesian.lean`,
please try to change them in sync.

## Main definitions

`IsCocartesian p f φ` expresses that `φ` is a co-Cartesian morphism lying over `f : R ⟶ S` with
respect to `p`. This means that for any morphism `φ' : a ⟶ b'` lying over `f` there
is a unique morphism `τ : b ⟶ b'` lying over `𝟙 S`, such that `φ' = φ ≫ τ`.

`IsStronglyCocartesian p f φ` expresses that `φ` is a strongly co-Cartesian morphism lying over `f`
with respect to `p`.

## Implementation

The constructor of `IsStronglyCocartesian` has been named `universal_property'`, and is mainly
intended to be used for constructing instances of this class. To use the universal property, we
generally recommended to use the lemma `IsStronglyCocartesian.universal_property` instead. The
difference between the two is that the latter is more flexible with respect to non-definitional
equalities.

-/

universe v₁ v₂ u₁ u₂

open CategoryTheory Functor Category IsHomLift

namespace CategoryTheory.Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮)

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)

class IsCocartesian : Prop where
  [toIsHomLift : IsHomLift p f φ]
  universal_property {b' : 𝒳} (φ' : a ⟶ b') [IsHomLift p f φ'] :
      ∃! χ : b ⟶ b', IsHomLift p (𝟙 S) χ ∧ φ ≫ χ = φ'

attribute [instance] IsCocartesian.toIsHomLift
