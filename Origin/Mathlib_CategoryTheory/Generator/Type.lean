/-
Extracted from CategoryTheory/Generator/Type.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Generator of Type

In this file, we show that `PUnit` is a separator of the category `Type u`.

-/

universe u

namespace CategoryTheory

lemma Types.isSeparator_punit : IsSeparator (PUnit.{u + 1}) := by
  intro X Y f g h
  ext x
  exact ConcreteCategory.congr_hom (h PUnit (by simp) (TypeCat.ofHom (fun _ ↦ x)))
    .unit

end CategoryTheory
