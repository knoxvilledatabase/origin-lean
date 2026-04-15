/-
Extracted from CategoryTheory/Localization/Resolution.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Resolutions for a morphism of localizers

Given a morphism of localizers `Φ : LocalizerMorphism W₁ W₂` (i.e. `W₁` and `W₂` are
morphism properties on categories `C₁` and `C₂`, and we have a functor
`Φ.functor : C₁ ⥤ C₂` which sends morphisms in `W₁` to morphisms in `W₂`), we introduce
the notion of right resolutions of objects in `C₂`, for `X₂ : C₂`.
A right resolution consists of an object `X₁ : C₁` and a morphism
`w : X₂ ⟶ Φ.functor.obj X₁` that is in `W₂`. Then, the typeclass
`Φ.HasRightResolutions` holds when any `X₂ : C₂` has a right resolution.

The type of right resolutions `Φ.RightResolution X₂` is endowed with a category
structure.

Similar definitions are done for left resolutions.

## Future work

* show that if `C` is an abelian category with enough injectives, there is a derivability
  structure associated to the inclusion of the full subcategory of complexes of injective
  objects into the bounded below homotopy category of `C` (TODO @joelriou)
* formalize dual results

## References
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

universe v₁ v₂ v₂' u₁ u₂ u₂'

namespace CategoryTheory

open Category Localization

variable {C₁ C₂ D₂ H : Type*} [Category* C₁] [Category* C₂] [Category* D₂] [Category* H]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂)

structure RightResolution (X₂ : C₂) where
  /-- an object in the source category -/
  {X₁ : C₁}
  /-- a morphism to an object of the form `Φ.functor.obj X₁` -/
  w : X₂ ⟶ Φ.functor.obj X₁
  hw : W₂ w

structure LeftResolution (X₂ : C₂) where
  /-- an object in the source category -/
  {X₁ : C₁}
  /-- a morphism from an object of the form `Φ.functor.obj X₁` -/
  w : Φ.functor.obj X₁ ⟶ X₂
  hw : W₂ w

variable {Φ X₂} in

lemma RightResolution.mk_surjective (R : Φ.RightResolution X₂) :
    ∃ (X₁ : C₁) (w : X₂ ⟶ Φ.functor.obj X₁) (hw : W₂ w), R = RightResolution.mk w hw :=
  ⟨_, R.w, R.hw, rfl⟩

variable {Φ X₂} in

lemma LeftResolution.mk_surjective (L : Φ.LeftResolution X₂) :
    ∃ (X₁ : C₁) (w : Φ.functor.obj X₁ ⟶ X₂) (hw : W₂ w), L = LeftResolution.mk w hw :=
  ⟨_, L.w, L.hw, rfl⟩

abbrev HasRightResolutions := ∀ (X₂ : C₂), Nonempty (Φ.RightResolution X₂)

abbrev HasLeftResolutions := ∀ (X₂ : C₂), Nonempty (Φ.LeftResolution X₂)

namespace RightResolution

variable {Φ} {X₂ : C₂}
