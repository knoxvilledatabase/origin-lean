/-
Extracted from CategoryTheory/Preadditive/Projective/LiftingProperties.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Characterization of projective objects in terms of lifting properties

An object `P` is projective iff the morphism `0 ⟶ P` has the
left lifting property with respect to epimorphisms,
`projective_iff_llp_epimorphisms_zero`.

-/

universe v u

namespace CategoryTheory

open Limits ZeroObject

variable {C : Type u} [Category.{v} C]

namespace Projective

lemma hasLiftingProperty_of_isZero
    {Z P X Y : C} (i : Z ⟶ P) (p : X ⟶ Y) [Epi p] [Projective P] (hZ : IsZero Z) :
    HasLiftingProperty i p where
  sq_hasLift {f g} sq := ⟨⟨{
    l := Projective.factorThru g p
    fac_left := hZ.eq_of_src _ _ }⟩⟩

-- INSTANCE (free from Core): {X

end Projective

lemma projective_iff_llp_epimorphisms_zero
    [HasZeroMorphisms C] [HasZeroObject C] (P : C) :
    Projective P ↔ (MorphismProperty.epimorphisms C).llp (0 : 0 ⟶ P) :=
  projective_iff_llp_epimorphisms_of_isZero _ (isZero_zero C)

end CategoryTheory
