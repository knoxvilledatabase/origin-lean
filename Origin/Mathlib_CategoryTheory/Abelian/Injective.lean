/-
Extracted from CategoryTheory/Abelian/Injective.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Preadditive.Yoneda.Injective
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Injective objects in abelian categories

* Objects in an abelian categories are injective if and only if the preadditive Yoneda functor
  on them preserves finite colimits.
-/

noncomputable section

open CategoryTheory Limits Injective Opposite

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

instance preservesHomology_preadditiveYonedaObj_of_injective (J : C) [hJ : Injective J] :
    (preadditiveYonedaObj J).PreservesHomology  := by
  letI := (injective_iff_preservesEpimorphisms_preadditive_yoneda_obj' J).mp hJ
  apply Functor.preservesHomology_of_preservesEpis_and_kernels

instance preservesFiniteColimits_preadditiveYonedaObj_of_injective (J : C) [hP : Injective J] :
    PreservesFiniteColimits (preadditiveYonedaObj J) := by
  apply Functor.preservesFiniteColimits_of_preservesHomology

theorem injective_of_preservesFiniteColimits_preadditiveYonedaObj (J : C)
    [hP : PreservesFiniteColimits (preadditiveYonedaObj J)] : Injective J := by
  rw [injective_iff_preservesEpimorphisms_preadditive_yoneda_obj']
  have := Functor.preservesHomologyOfExact (preadditiveYonedaObj J)
  infer_instance

end CategoryTheory
