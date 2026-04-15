/-
Extracted from CategoryTheory/PathCategory/MorphismProperty.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Properties of morphisms in a path category.

We provide a formulation of induction principles for morphisms in a path category in terms of
`MorphismProperty`. This file is separate from `Mathlib/CategoryTheory/PathCategory/Basic.lean` in
order to reduce transitive imports. -/

universe v₁ u₁

namespace CategoryTheory.Paths

variable (V : Type u₁) [Quiver.{v₁} V]

lemma morphismProperty_eq_top
    (P : MorphismProperty (Paths V))
    (id : ∀ {v : V}, P (𝟙 ((of V).obj v)))
    (comp : ∀ {u v w : V}
      (p : (of V).obj u ⟶ (of V).obj v) (q : v ⟶ w), P p → P (p ≫ (of V).map q)) :
    P = ⊤ := by
  ext; constructor
  · simp
  · exact fun _ ↦ induction (fun f ↦ P f) id comp _

lemma morphismProperty_eq_top'
    (P : MorphismProperty (Paths V))
    (id : ∀ {v : V}, P (𝟙 ((of V).obj v)))
    (comp : ∀ {u v w : V}
      (p : u ⟶ v) (q : (of V).obj v ⟶ (of V).obj w), P q → P ((of V).map p ≫ q)) :
    P = ⊤ := by
  ext; constructor
  · simp
  · exact fun _ ↦ induction' (fun f ↦ P f) id comp _

lemma morphismProperty_eq_top_of_isMultiplicative (P : MorphismProperty (Paths V))
    [P.IsMultiplicative]
    (hP : ∀ {u v : V} (p : u ⟶ v), P ((of V).map p)) : P = ⊤ :=
  morphismProperty_eq_top _ _ (P.id_mem _) (fun _ q hp ↦ P.comp_mem _ _ hp (hP q))

end

variable {C : Type*} [Category* C] {V : Type u₁} [Quiver.{v₁} V]
