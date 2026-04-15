/-
Extracted from CategoryTheory/ObjectProperty/HasCardinalLT.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Properties of objects that are bounded by a cardinal

Given `P : ObjectProperty C` and `κ : Cardinal`, we introduce a predicate
`P.HasCardinalLT κ` saying that the cardinality of `Subtype P` is `< κ`.

-/

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace ObjectProperty

protected abbrev HasCardinalLT (P : ObjectProperty C) (κ : Cardinal.{w}) :=
    _root_.HasCardinalLT (Subtype P) κ

lemma HasCardinalLT.iSup
    {ι : Type*} {P : ι → ObjectProperty C} {κ : Cardinal.{w}} [Fact κ.IsRegular]
    (hP : ∀ i, (P i).HasCardinalLT κ) (hι : HasCardinalLT ι κ) :
    (⨆ i, P i).HasCardinalLT κ :=
  hasCardinalLT_subtype_iSup _ hι hP

lemma HasCardinalLT.sup
    {P₁ P₂ : ObjectProperty C} {κ : Cardinal.{w}}
    (h₁ : P₁.HasCardinalLT κ) (h₂ : P₂.HasCardinalLT κ)
    (hκ : Cardinal.aleph0 ≤ κ) :
    (P₁ ⊔ P₂).HasCardinalLT κ :=
  hasCardinalLT_union hκ h₁ h₂

end ObjectProperty

end CategoryTheory
