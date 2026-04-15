/-
Extracted from Algebra/Category/ModuleCat/Sheaf/Localization.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The category of sheaves of modules as a localization of presheaves of modules

Similarly as the category of sheaves with values in a category identify to
a localization of the category of presheaves with respect to those morphisms
which become isomorphisms after sheafification
(see the file `Mathlib/CategoryTheory/Sites/Localization.lean`), we show that
the sheafification functor from presheaves of modules to sheaves of modules
is a localization functor.

-/

universe v u v' u'

open CategoryTheory

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

namespace PresheafOfModules

variable {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasWeakSheafify J AddCommGrpCat.{v}]

open MorphismProperty in

lemma inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms :
    J.W.inverseImage (toPresheaf R₀) = (isomorphisms _).inverseImage (sheafification α) := by
  rw [J.W_eq_inverseImage_isomorphisms]
  ext P Q f
  simp only [inverseImage_iff, isomorphisms.iff,
    ← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf.{v} R)]
  exact (isomorphisms _).arrow_mk_iso_iff
    (((Functor.mapArrowFunctor _ _).mapIso (sheafificationCompToSheaf.{v} α)).app (Arrow.mk f))

-- INSTANCE (free from Core): :

end PresheafOfModules
