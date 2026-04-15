/-
Extracted from CategoryTheory/Preadditive/Injective/LiftingProperties.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Characterization of injective objects in terms of lifting properties

An object `I` is injective iff the morphism `I ⟶ 0` has the
right lifting property with respect to monomorphisms,
`injective_iff_rlp_monomorphisms_zero`.

-/

universe v u

namespace CategoryTheory

open Limits ZeroObject

variable {C : Type u} [Category.{v} C]

namespace Injective

lemma hasLiftingProperty_of_isZero
    {A B I Z : C} (i : A ⟶ B) [Mono i] [Injective I] (p : I ⟶ Z) (hZ : IsZero Z) :
    HasLiftingProperty i p where
  sq_hasLift {f g} sq := ⟨⟨{
    l := Injective.factorThru f i
    fac_right := hZ.eq_of_tgt _ _ }⟩⟩

-- INSTANCE (free from Core): {A

end Injective

lemma injective_iff_rlp_monomorphisms_zero
    [HasZeroMorphisms C] [HasZeroObject C] (I : C) :
    Injective I ↔ (MorphismProperty.monomorphisms C).rlp (0 : I ⟶ 0) :=
  injective_iff_rlp_monomorphisms_of_isZero _ (isZero_zero C)

end CategoryTheory
