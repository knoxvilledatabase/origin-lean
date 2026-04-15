/-
Extracted from CategoryTheory/Subobject/Limits.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Specific subobjects

We define `equalizerSubobject`, `kernelSubobject` and `imageSubobject`, which are the subobjects
represented by the equalizer, kernel and image of (a pair of) morphism(s) and provide conditions
for `P.factors f`, where `P` is one of these special subobjects.

TODO: an iff characterisation of `(imageSubobject f).Factors h`

-/

universe v u

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Subobject Opposite

variable {C : Type u} [Category.{v} C] {X Y Z : C}

namespace CategoryTheory

namespace Limits

section Pullback

variable {W : C} (f : X ⟶ Y) [HasPullbacks C]

theorem pullback_factors (y : Subobject Y) (h : W ⟶ X) (hF : y.Factors (h ≫ f)) :
    Subobject.Factors ((Subobject.pullback f).obj y) h :=
  let h' := Subobject.factorThru _ _ hF
  let w := Subobject.factorThru_arrow _ _ hF
  (factors_iff _ _).mpr
    ⟨(Subobject.isPullback f y).lift h' h w,
      (Subobject.isPullback f y).lift_snd h' h w⟩

theorem pullback_factors_iff (y : Subobject Y) (h : W ⟶ X) :
    Subobject.Factors ((Subobject.pullback f).obj y) h ↔ y.Factors (h ≫ f) := by
  refine ⟨fun hf ↦ ?_, fun hF ↦ pullback_factors f y h hF⟩
  rw [factors_iff]
  use Subobject.factorThru _ _ hf ≫ Subobject.pullbackπ f y
  simp [(Subobject.isPullback f y).w]

end Pullback

section Equalizer

variable (f g : X ⟶ Y) [HasEqualizer f g]

abbrev equalizerSubobject : Subobject X :=
  Subobject.mk (equalizer.ι f g)

def equalizerSubobjectIso : (equalizerSubobject f g : C) ≅ equalizer f g :=
  Subobject.underlyingIso (equalizer.ι f g)
