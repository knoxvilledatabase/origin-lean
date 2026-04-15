/-
Extracted from CategoryTheory/Abelian/Injective/Basic.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Injective objects in abelian categories

* Objects in an abelian category are injective if and only if the preadditive Yoneda functor
  on them preserves finite colimits.
-/

noncomputable section

open CategoryTheory Limits Injective Opposite

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

-- INSTANCE (free from Core): preservesHomology_preadditiveYonedaObj_of_injective

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): preservesFiniteColimits_preadditiveYonedaObj_of_injective

theorem injective_of_preservesFiniteColimits_preadditiveYonedaObj (J : C)
    [hP : PreservesFiniteColimits (preadditiveYonedaObj J)] : Injective J := by
  rw [injective_iff_preservesEpimorphisms_preadditive_yoneda_obj']
  have := Functor.preservesHomologyOfExact (preadditiveYonedaObj J)
  infer_instance

end CategoryTheory
