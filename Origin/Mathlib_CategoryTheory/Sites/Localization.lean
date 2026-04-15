/-
Extracted from CategoryTheory/Sites/Localization.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The sheaf category as a localized category

In this file, it is shown that the category of sheaves `Sheaf J A` is a localization
of the category `Presheaf J A` with respect to the class `J.W` of morphisms
of presheaves which become isomorphisms after applying the sheafification functor.

-/

universe w

namespace CategoryTheory

open Localization

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) {A : Type*} [Category* A]

namespace GrothendieckTopology

abbrev W : MorphismProperty (Cᵒᵖ ⥤ A) := ObjectProperty.isLocal (Presheaf.IsSheaf J)

variable (A) in

lemma W_eq_isLocal_range_sheafToPresheaf_obj :
    J.W = ObjectProperty.isLocal (· ∈ Set.range (sheafToPresheaf J A).obj) := by
  apply congr_arg
  ext P
  constructor
  · intro hP
    exact ⟨⟨P, hP⟩, rfl⟩
  · rintro ⟨F, rfl⟩
    exact F.property
