/-
Extracted from CategoryTheory/ObjectProperty/Equivalence.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Equivalence of full subcategories

The inclusion functor `P.FullSubcategory ⥤ Q.FullSubcategory` induced
by an inequality `P ≤ Q` in `ObjectProperty C` is an equivalence iff
`Q ≤ P.isoClosure`.

-/

universe v v' u u'

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] {P Q : ObjectProperty C} (h : P ≤ Q)

lemma essSurj_ιOfLE_iff : (ιOfLE h).EssSurj ↔ Q ≤ P.isoClosure := by
  refine ⟨fun _ X hX ↦ ?_, fun hPQ ↦ ⟨fun ⟨Y, hY⟩ ↦ ?_⟩⟩
  · exact ⟨_, ((ιOfLE h).objPreimage ⟨X, hX⟩).2,
      ⟨Q.ι.mapIso ((ιOfLE h).objObjPreimageIso ⟨X, hX⟩).symm⟩⟩
  · obtain ⟨X, hX, ⟨e⟩⟩ := hPQ _ hY
    exact ⟨⟨X, hX⟩, ⟨Q.ι.preimageIso e.symm⟩⟩

lemma isEquivalence_ιOfLE_iff : (ιOfLE h).IsEquivalence ↔ Q ≤ P.isoClosure := by
  rw [← essSurj_ιOfLE_iff h]
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ { }⟩

-- INSTANCE (free from Core): :

variable (C) in
