/-
Extracted from CategoryTheory/Localization/DerivabilityStructure/OfFunctorialResolutions.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Functorial resolutions give derivability structures

In this file, we provide a constructor for right derivability structures.
We assume that `Φ : LocalizerMorphism W₁ W₂` is given by
a fully faithful functor `Φ.functor : C₁ ⥤ C₂` and that we have a resolution
functor `ρ : C₂ ⥤ C₁` with a natural transformation `i : 𝟭 C₂ ⟶ ρ ⋙ Φ.functor`
such that `W₂ (i.app X₂)` for any `X₂ : C₂`. If we assume
that `W₁` is induced by `W₂`, that `W₂` is multiplicative and has
the two-out-of-three property, then `Φ` is a right derivability structure.

-/

namespace CategoryTheory

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂)
  {ρ : C₂ ⥤ C₁} (i : 𝟭 C₂ ⟶ ρ ⋙ Φ.functor) (hi : ∀ X₂, W₂ (i.app X₂))
  (hW₁ : W₁ = W₂.inverseImage Φ.functor)

include hi in

lemma hasRightResolutions_arrow_of_functorial_resolutions :
    Φ.arrow.HasRightResolutions :=
  fun f ↦
    ⟨{ X₁ := Arrow.mk (ρ.map f.hom)
       w := Arrow.homMk (i.app _) (i.app _) (i.naturality f.hom).symm
       hw := ⟨hi _, hi _⟩ }⟩

namespace functorialRightResolutions

open Functor

variable {Φ i}

set_option backward.isDefEq.respectTransparency false in
