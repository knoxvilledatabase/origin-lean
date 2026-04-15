/-
Extracted from CategoryTheory/PathCategory/MorphismProperty.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Properties of morphisms in a path category.

We provide a formulation of induction principles for morphisms in a path category in terms of
`MorphismProperty`. This file is separate from `CategoryTheory.PathCategory.Basic` in order to
reduce transitive imports. -/

universe v₁ u₁

namespace CategoryTheory.Paths

variable (V : Type u₁) [Quiver.{v₁ + 1} V]

lemma morphismProperty_eq_top
    (P : MorphismProperty (Paths V))
    (id : ∀ {v : V}, P (𝟙 (of.obj v)))
    (comp : ∀ {u v w : V} (p : of.obj u ⟶ of.obj v) (q : v ⟶ w), P p → P (p ≫ of.map q)) :
    P = ⊤ := by
  ext; constructor
  · simp
  · exact fun _ ↦ induction (fun f ↦ P f) id comp _

lemma morphismProperty_eq_top'
    (P : MorphismProperty (Paths V))
    (id : ∀ {v : V}, P (𝟙 (of.obj v)))
    (comp : ∀ {u v w : V} (p : u ⟶ v) (q : of.obj v ⟶ of.obj w), P q → P (of.map p ≫ q)) :
    P = ⊤ := by
  ext; constructor
  · simp
  · exact fun _ ↦ induction' (fun f ↦ P f) id comp _

end CategoryTheory.Paths
