/-
Extracted from CategoryTheory/Functor/TypeValuedFlat.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Type-valued flat functors

A functor `F : C ⥤ Type w` is a flat Type-valued functor if the category
`F.Elements` is cofiltered. (This is not equivalent to saying that `F`
is representably flat in the sense of the typeclass `RepresentablyFlat`
defined in the file `Mathlib/CategoryTheory/Functor/Flat.lean`, see also
https://golem.ph.utexas.edu/category/2011/06/flat_functors_and_morphisms_of.html
for a clarification about the differences between these notions.)

In this file, we show that if finite limits exist in `C` and are preserved by `F`,
then `F.Elements` is cofiltered.

-/

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

lemma Functor.isCofiltered_elements
    (F : C ⥤ Type w) [HasFiniteLimits C] [PreservesFiniteLimits F] :
    IsCofiltered F.Elements where
  nonempty := ⟨⊤_ C, (terminalIsTerminal.isTerminalObj F).from PUnit .unit⟩
  cone_objs := by
    rintro ⟨X, x⟩ ⟨Y, y⟩
    let h := mapIsLimitOfPreservesOfIsLimit F _ _ (prodIsProd X Y)
    let h' := Types.binaryProductLimit (F.obj X) (F.obj Y)
    exact ⟨⟨X ⨯ Y, (h'.conePointUniqueUpToIso h).hom ⟨x, y⟩⟩,
      ⟨prod.fst, ConcreteCategory.congr_hom (h'.conePointUniqueUpToIso_hom_comp h (.mk .left)) _⟩,
      ⟨prod.snd, ConcreteCategory.congr_hom (h'.conePointUniqueUpToIso_hom_comp h (.mk .right)) _⟩,
      by tauto⟩
  cone_maps := by
    rintro ⟨X, x⟩ ⟨Y, y⟩ ⟨f, hf⟩ ⟨g, hg⟩
    dsimp at f g hf hg
    rw [← hg] at hf
    let h := isLimitForkMapOfIsLimit F _ (equalizerIsEqualizer f g)
    let h' := (Types.equalizerLimit (g := F.map f) (h := F.map g)).isLimit
    exact ⟨⟨equalizer f g, (h'.conePointUniqueUpToIso h).hom ⟨x, hf⟩⟩,
      ⟨equalizer.ι f g, ConcreteCategory.congr_hom
        (h'.conePointUniqueUpToIso_hom_comp h .zero) ⟨x, hf⟩⟩,
      by ext; exact equalizer.condition f g⟩

namespace FunctorToTypes

variable (F : C ⥤ Type w) {X : C} (x : F.obj X)

set_option backward.isDefEq.respectTransparency false in

def fromOverSubfunctor : Subfunctor (Over.forget X ⋙ F) where
  obj U := F.map U.hom ⁻¹' {x}
  map _ _ _ := by simpa [← comp_apply, ← Functor.map_comp]
