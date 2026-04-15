/-
Extracted from CategoryTheory/MorphismProperty/HasCardinalLT.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Properties of morphisms that are bounded by a cardinal

Given `P : MorphismProperty C` and `κ : Cardinal`, we introduce a predicate
`P.HasCardinalLT κ` saying that the cardinality of `P.toSet` is `< κ`.

-/

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

protected abbrev HasCardinalLT (P : MorphismProperty C) (κ : Cardinal.{w}) :=
    _root_.HasCardinalLT P.toSet κ

lemma HasCardinalLT.iSup
    {ι : Type*} {P : ι → MorphismProperty C} {κ : Cardinal.{w}} [Fact κ.IsRegular]
    (hP : ∀ i, (P i).HasCardinalLT κ) (hι : HasCardinalLT ι κ) :
    (⨆ i, P i).HasCardinalLT κ := by
  dsimp only [MorphismProperty.HasCardinalLT]
  rw [toSet_iSup]
  exact hasCardinalLT_iUnion _ hι hP

lemma HasCardinalLT.sup
    {P₁ P₂ : MorphismProperty C} {κ : Cardinal.{w}}
    (h₁ : P₁.HasCardinalLT κ) (h₂ : P₂.HasCardinalLT κ)
    (hκ : Cardinal.aleph0 ≤ κ) :
    (P₁ ⊔ P₂).HasCardinalLT κ := by
  dsimp only [MorphismProperty.HasCardinalLT]
  rw [MorphismProperty.toSet_max]
  exact hasCardinalLT_union hκ h₁ h₂

end MorphismProperty

end CategoryTheory
