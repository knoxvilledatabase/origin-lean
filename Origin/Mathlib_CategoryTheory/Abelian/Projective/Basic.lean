/-
Extracted from CategoryTheory/Abelian/Projective/Basic.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Projective objects in abelian categories

In an abelian category, an object `P` is projective iff the functor
`preadditiveCoyonedaObj P` preserves finite colimits.

-/

universe v u

namespace CategoryTheory

open Limits Projective Opposite

variable {C : Type u} [Category.{v} C] [Abelian C]

-- INSTANCE (free from Core): preservesHomology_preadditiveCoyonedaObj_of_projective

-- INSTANCE (free from Core): preservesFiniteColimits_preadditiveCoyonedaObj_of_projective

theorem projective_of_preservesFiniteColimits_preadditiveCoyonedaObj (P : C)
    [hP : PreservesFiniteColimits (preadditiveCoyonedaObj P)] : Projective P := by
  rw [projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj]
  have := Functor.preservesHomologyOfExact (preadditiveCoyonedaObj P)
  infer_instance

end CategoryTheory
