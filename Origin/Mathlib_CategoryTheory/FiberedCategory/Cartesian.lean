/-
Extracted from CategoryTheory/FiberedCategory/Cartesian.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cartesian morphisms

This file defines Cartesian resp. strongly Cartesian morphisms with respect to a functor
`p : 𝒳 ⥤ 𝒮`.

This file has been adapted to `Mathlib/CategoryTheory/FiberedCategory/Cocartesian.lean`,
please try to change them in sync.

## Main definitions

`IsCartesian p f φ` expresses that `φ` is a Cartesian morphism lying over `f` with respect to `p` in
the sense of SGA 1 VI 5.1. This means that for any morphism `φ' : a' ⟶ b` lying over `f` there is
a unique morphism `τ : a' ⟶ a` lying over `𝟙 R`, such that `φ' = τ ≫ φ`.

`IsStronglyCartesian p f φ` expresses that `φ` is a strongly Cartesian morphism lying over `f` with
respect to `p`, see <https://stacks.math.columbia.edu/tag/02XK>.

## Implementation

The constructor of `IsStronglyCartesian` has been named `universal_property'`, and is mainly
intended to be used for constructing instances of this class. To use the universal property, we
generally recommended to use the lemma `IsStronglyCartesian.universal_property` instead. The
difference between the two is that the latter is more flexible with respect to non-definitional
equalities.

## References
* [A. Grothendieck, M. Raynaud, *SGA 1*](https://arxiv.org/abs/math/0206203)
* [Stacks: Fibred Categories](https://stacks.math.columbia.edu/tag/02XJ)
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory Functor Category IsHomLift

namespace CategoryTheory.Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮)

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)

class IsCartesian : Prop where
  [toIsHomLift : IsHomLift p f φ]
  universal_property {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ'] :
      ∃! χ : a' ⟶ a, IsHomLift p (𝟙 R) χ ∧ χ ≫ φ = φ'

attribute [instance] IsCartesian.toIsHomLift
