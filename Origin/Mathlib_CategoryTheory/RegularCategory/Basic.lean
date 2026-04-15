/-
Extracted from CategoryTheory/RegularCategory/Basic.lean
Genuine: 5 of 14 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core

/-!
# Regular categories

A regular category is a category with finite limits such that each kernel pair has a coequalizer
and such that regular epimorphisms are stable under pullback.

These categories provide a good ground to develop the calculus of relations, as well as being the
semantics for regular logic.

## Main results

* We show that every regular category has strong epi-mono factorisations, following Theorem 1.11
  in [Gran2021].
* We show that every regular category satisfies Frobenius reciprocity. That is, that in their
  internal language, we have `∃ x, (P(x) ⊓ Q)` iff `(∃ x, P(x)) ⊓ Q`, for a proposition `Q` not
  depending on `x`.

## Future work
* Show that every topos is regular
* Show that regular logic has an interpretation in regular categories

## References
* [Marino Gran, An Introduction to Regular Categories][Gran2021]
* <https://ncatlab.org/nlab/show/regular+category>
-/

open CategoryTheory Limits

universe u v

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

class Regular extends HasFiniteLimits C where
  hasCoequalizer_of_isKernelPair {X Y Z : C} {f : X ⟶ Y} {g₁ g₂ : Z ⟶ X} :
    IsKernelPair f g₁ g₂ → HasCoequalizer g₁ g₂
  regularEpiIsStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange (.regularEpi C)

variable {C} [Regular C]

-- INSTANCE (free from Core): {X

-- INSTANCE (free from Core): {X

-- INSTANCE (free from Core): :

variable {X Y : C} (f : X ⟶ Y)

namespace Regular

section StrongEpiMonoFactorisation

-- INSTANCE (free from Core): :

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): :

set_option backward.isDefEq.respectTransparency false in

noncomputable def strongEpiMonoFactorisation : StrongEpiMonoFactorisation f where
  I := coequalizer (pullback.fst f f) (pullback.snd f f)
  m := coequalizer.desc f pullback.condition
  e := coequalizer.π (pullback.fst f f) (pullback.snd f f)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): hasStrongEpiMonoFactorisations

set_option backward.isDefEq.respectTransparency false in

noncomputable def regularEpiOfExtremalEpi [h : ExtremalEpi f] : RegularEpi f :=
  have := h.isIso (strongEpiMonoFactorisation f).e (strongEpiMonoFactorisation f).m (by simp)
  RegularEpi.ofArrowIso (Arrow.isoMk (f := .mk (strongEpiMonoFactorisation f).e) (Iso.refl _)
    (asIso (strongEpiMonoFactorisation f).m)) (IsRegularEpi.getStruct _)

-- INSTANCE (free from Core): isRegularEpi_of_extremalEpi

end StrongEpiMonoFactorisation

section Frobenius

open Subobject

variable {A B : C} (f : A ⟶ B) (A' : Subobject A) (B' : Subobject B)

set_option backward.isDefEq.respectTransparency false in

noncomputable def frobeniusMorphism :
    underlying.obj (A' ⊓ (Subobject.pullback f).obj B') ⟶
      underlying.obj ((«exists» f).obj A' ⊓ B') :=
  (inf_isPullback ((«exists» f).obj A') B').flip.lift
    ((ofLE _ _ (inf_le_right A' ((Subobject.pullback f).obj B'))) ≫ (pullbackπ _ _))
    ((ofLE _ _ (inf_le_left A' ((Subobject.pullback f).obj B'))) ≫ (imageFactorisation f A').F.e)
    (by simp [← imageFactorisation_F_m, (isPullback _ _).w])

set_option backward.isDefEq.respectTransparency false in

lemma frobeniusMorphism_isPullback :
    IsPullback (frobeniusMorphism f A' B')
      ((ofLE _ _ (inf_le_left A' ((Subobject.pullback f).obj B'))))
      ((ofLE _ _ (inf_le_left ((«exists» f).obj A') B')))
      (imageFactorisation _ _).F.e := by
  apply IsPullback.of_right (t := (inf_isPullback ((«exists» f).obj A') B').flip)
    (p := by simp [frobeniusMorphism])
  simpa [frobeniusMorphism, IsPullback.lift_fst, ← imageFactorisation_F_m,
    (isPullback f B').paste_horiz_iff] using
    (inf_isPullback A' ((Subobject.pullback f).obj B')).flip

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): :

set_option backward.isDefEq.respectTransparency false in
