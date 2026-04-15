/-
Extracted from CategoryTheory/Localization/Predicate.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Predicate for localized categories

In this file, a predicate `L.IsLocalization W` is introduced for a functor `L : C ⥤ D`
and `W : MorphismProperty C`: it expresses that `L` identifies `D` with the localized
category of `C` with respect to `W` (up to equivalence).

We introduce a universal property `StrictUniversalPropertyFixedTarget L W E` which
states that `L` inverts the morphisms in `W` and that all functors `C ⥤ E` inverting
`W` uniquely factor as a composition of `L ⋙ G` with `G : D ⥤ E`. Such universal
properties are inputs for the constructor `IsLocalization.mk'` for `L.IsLocalization W`.

When `L : C ⥤ D` is a localization functor for `W : MorphismProperty` (i.e. when
`[L.IsLocalization W]` holds), for any category `E`, there is
an equivalence `FunctorEquivalence L W E : (D ⥤ E) ≌ (W.FunctorsInverting E)`
that is induced by the composition with the functor `L`. When two functors
`F : C ⥤ E` and `F' : D ⥤ E` correspond via this equivalence, we shall say
that `F'` lifts `F`, and the associated isomorphism `L ⋙ F' ≅ F` is the
datum that is part of the class `Lifting L W F F'`. The functions
`liftNatTrans` and `liftNatIso` can be used to lift natural transformations
and natural isomorphisms between functors.

-/

noncomputable section

namespace CategoryTheory

open Category Functor

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) (W : MorphismProperty C) (E : Type*)
  [Category* E]

namespace Functor

class IsLocalization : Prop where
  /-- the functor inverts the given `MorphismProperty` -/
  inverts : W.IsInvertedBy L
  /-- the induced functor from the constructed localized category is an equivalence -/
  isEquivalence : IsEquivalence (Localization.Construction.lift L inverts)

-- INSTANCE (free from Core): q_isLocalization

end Functor

namespace Localization

structure StrictUniversalPropertyFixedTarget where
  /-- the functor `L` inverts `W` -/
  inverts : W.IsInvertedBy L
  /-- any functor `C ⥤ E` which inverts `W` can be lifted as a functor `D ⥤ E` -/
  lift : ∀ (F : C ⥤ E) (_ : W.IsInvertedBy F), D ⥤ E
  /-- there is a factorisation involving the lifted functor -/
  fac : ∀ (F : C ⥤ E) (hF : W.IsInvertedBy F), L ⋙ lift F hF = F
  /-- uniqueness of the lifted functor -/
  uniq : ∀ (F₁ F₂ : D ⥤ E) (_ : L ⋙ F₁ = L ⋙ F₂), F₁ = F₂
