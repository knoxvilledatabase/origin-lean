/-
Extracted from CategoryTheory/MorphismProperty/OfObjectProperty.lean
Genuine: 4 of 8 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Morphism properties from object properties

Given two object properties `P` and `Q`, we introduce a morphism property
`ofObjectProperty P Q`, given by all morphisms whose source satisfies `P` and
target satisfies `Q`.

-/

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category* C]

def ofObjectProperty (P Q : ObjectProperty C) : MorphismProperty C := fun X Y _ => P X ∧ Q Y

variable (P Q : ObjectProperty C)

variable {P} in

lemma monotone_ofObjectProperty_left {P' : ObjectProperty C} (h : P ≤ P') :
    ofObjectProperty P Q ≤ ofObjectProperty P' Q := by
  intro _ _ _ ⟨hX, hY⟩
  exact ⟨h _ hX, hY⟩

variable {Q} in

lemma monotone_ofObjectProperty_right {Q' : ObjectProperty C} (h : Q ≤ Q') :
    ofObjectProperty P Q ≤ ofObjectProperty P Q' := by
  intro _ _ _ ⟨hX, hY⟩
  exact ⟨hX, h _ hY⟩

lemma ofObjectProperty_map_le {D : Type*} [Category* D] (F : C ⥤ D) :
    (ofObjectProperty P Q).map F ≤ ofObjectProperty (P.map F) (Q.map F) := by
  intro X Y f ⟨X', Y', f', ⟨hX', hY'⟩, ⟨i⟩⟩
  exact ⟨⟨X', hX', ⟨Comma.leftIso i⟩⟩, ⟨Y', hY', ⟨Comma.rightIso i⟩⟩⟩

-- INSTANCE (free from Core): [P.IsClosedUnderIsomorphisms]

-- INSTANCE (free from Core): [Q.IsClosedUnderIsomorphisms]

end CategoryTheory.MorphismProperty
