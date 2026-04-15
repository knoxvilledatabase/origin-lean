/-
Extracted from CategoryTheory/ObjectProperty/Extensions.lean
Genuine: 3 of 6 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Properties of objects that are closed under extensions

Given a category `C` and `P : ObjectProperty C`, we define a type
class `P.IsClosedUnderExtensions` expressing that the property
is closed under extensions.

-/

universe v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace ObjectProperty

variable (P : ObjectProperty C)

variable [HasZeroMorphisms C]

class IsClosedUnderExtensions : Prop where
  prop_X₂_of_shortExact {S : ShortComplex C} (hS : S.ShortExact)
      (h₁ : P S.X₁) (h₃ : P S.X₃) : P S.X₂

lemma prop_X₂_of_shortExact [P.IsClosedUnderExtensions]
    {S : ShortComplex C} (hS : S.ShortExact)
    (h₁ : P S.X₁) (h₃ : P S.X₃) : P S.X₂ :=
  IsClosedUnderExtensions.prop_X₂_of_shortExact hS h₁ h₃

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): [P.IsClosedUnderExtensions]

end

lemma prop_biprod {X₁ X₂ : C} (h₁ : P X₁) (h₂ : P X₂) [Preadditive C] [HasZeroObject C]
    [P.IsClosedUnderExtensions] [HasBinaryBiproduct X₁ X₂] :
    P (X₁ ⊞ X₂) :=
  P.prop_X₂_of_shortExact
    (ShortComplex.Splitting.ofHasBinaryBiproduct X₁ X₂).shortExact h₁ h₂

end ObjectProperty

end CategoryTheory
