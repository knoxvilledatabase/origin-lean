/-
Extracted from CategoryTheory/Shift/Localization.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The shift induced on a localized category

Let `C` be a category equipped with a shift by a monoid `A`. A morphism property `W`
on `C` satisfies `W.IsCompatibleWithShift A` when for all `a : A`,
a morphism `f` is in `W` iff `f⟦a⟧'` is. When this compatibility is satisfied,
then the corresponding localized category can be equipped with
a shift by `A`, and the localization functor is compatible with the shift.

-/

universe v₁ v₂ v₃ u₁ u₂ u₃ w

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  (A : Type w) [AddMonoid A] [HasShift C A]

namespace MorphismProperty

class IsCompatibleWithShift : Prop where
  /-- the condition that for all `a : A`, the morphism property `W` is not changed when
  we take its inverse image by the shift functor by `a` -/
  condition : ∀ (a : A), W.inverseImage (shiftFunctor C a) = W

variable [W.IsCompatibleWithShift A]

namespace IsCompatibleWithShift

variable {A}

lemma iff {X Y : C} (f : X ⟶ Y) (a : A) : W (f⟦a⟧') ↔ W f := by
  conv_rhs => rw [← @IsCompatibleWithShift.condition _ _ W A _ _ _ a]
  rfl

lemma shiftFunctor_comp_inverts (a : A) :
    W.IsInvertedBy (shiftFunctor C a ⋙ L) := fun _ _ f hf =>
  Localization.inverts L W _ (by simpa only [iff] using hf)

end IsCompatibleWithShift

variable {A} in

lemma shift {X Y : C} {f : X ⟶ Y} (hf : W f) (a : A) : W (f⟦a⟧') := by
  simpa only [IsCompatibleWithShift.iff W f a] using hf

variable {A} in

abbrev shiftLocalizerMorphism (a : A) : LocalizerMorphism W W where
  functor := shiftFunctor C a
  map := by rw [MorphismProperty.IsCompatibleWithShift.condition]

end MorphismProperty

variable [W.IsCompatibleWithShift A]
