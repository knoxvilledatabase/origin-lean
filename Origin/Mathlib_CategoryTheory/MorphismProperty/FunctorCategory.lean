/-
Extracted from CategoryTheory/MorphismProperty/FunctorCategory.lean
Genuine: 3 of 12 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core

/-!
# Stability properties of morphism properties on functor categories

Given `W : MorphismProperty C` and a category `J`, we study the
stability properties of `W.functorCategory J : MorphismProperty (J ⥤ C)`.

Under suitable assumptions, we also show that if monomorphisms
in `C` are stable under transfinite compositions (or coproducts),
then the same holds in the category `J ⥤ C`.

-/

universe v v' v'' u u' u''

namespace CategoryTheory

open Limits

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

-- INSTANCE (free from Core): [W.IsStableUnderRetracts]

variable {W}

-- INSTANCE (free from Core): IsStableUnderLimitsOfShape.functorCategory

-- INSTANCE (free from Core): IsStableUnderColimitsOfShape.functorCategory

-- INSTANCE (free from Core): [W.IsStableUnderBaseChange]

-- INSTANCE (free from Core): [W.IsStableUnderCobaseChange]

-- INSTANCE (free from Core): (K

variable (J : Type u'') [Category.{v''} J]

lemma functorCategory_isomorphisms :
    (isomorphisms C).functorCategory J = isomorphisms (J ⥤ C) := by
  ext _ _ f
  simp only [functorCategory, isomorphisms.iff, NatTrans.isIso_iff_isIso_app]

lemma functorCategory_monomorphisms [HasPullbacks C] :
    (monomorphisms C).functorCategory J = monomorphisms (J ⥤ C) := by
  ext _ _ f
  simp only [functorCategory, monomorphisms.iff, NatTrans.mono_iff_mono_app]

lemma functorCategory_epimorphisms [HasPushouts C] :
    (epimorphisms C).functorCategory J = epimorphisms (J ⥤ C) := by
  ext _ _ f
  simp only [functorCategory, epimorphisms.iff, NatTrans.epi_iff_epi_app]

-- INSTANCE (free from Core): (K

-- INSTANCE (free from Core): (K'

-- INSTANCE (free from Core): [IsStableUnderCoproducts.{u'}

end MorphismProperty

end CategoryTheory
