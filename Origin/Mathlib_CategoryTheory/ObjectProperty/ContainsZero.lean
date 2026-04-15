/-
Extracted from CategoryTheory/ObjectProperty/ContainsZero.lean
Genuine: 5 of 15 | Dissolved: 0 | Infrastructure: 10
-/
import Origin.Core

/-!
# Properties of objects which hold for a zero object

Given a category `C` and `P : ObjectProperty C`, we define a type class `P.ContainsZero`
expressing that there exists a zero object for which `P` holds. (We do not require
that `P` holds for all zero objects, as in some applications (e.g. triangulated categories),
`P` may not necessarily be closed under isomorphisms.)

-/

universe v v' u u'

namespace CategoryTheory

open Limits ZeroObject Opposite

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace ObjectProperty

variable (P Q : ObjectProperty C)

class ContainsZero : Prop where
  exists_zero : ∃ (Z : C), IsZero Z ∧ P Z

lemma exists_prop_of_containsZero [P.ContainsZero] :
    ∃ (Z : C), IsZero Z ∧ P Z :=
  ContainsZero.exists_zero

-- INSTANCE (free from Core): (priority

lemma prop_of_isZero [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    {Z : C} (hZ : IsZero Z) :
    P Z := by
  obtain ⟨Z₀, hZ₀, h₀⟩ := P.exists_prop_of_containsZero
  exact P.prop_of_iso (hZ₀.iso hZ) h₀

lemma prop_zero [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [HasZeroObject C] :
    P 0 :=
  P.prop_of_isZero (isZero_zero C)

-- INSTANCE (free from Core): [HasZeroObject

-- INSTANCE (free from Core): [HasZeroObject

-- INSTANCE (free from Core): [P.ContainsZero]

-- INSTANCE (free from Core): [P.ContainsZero]

-- INSTANCE (free from Core): [P.ContainsZero]

-- INSTANCE (free from Core): [P.ContainsZero]

-- INSTANCE (free from Core): [P.ContainsZero]

-- INSTANCE (free from Core): (P

-- INSTANCE (free from Core): [P.ContainsZero]

end ObjectProperty

abbrev Functor.kernel (F : C ⥤ D) : ObjectProperty C :=
  ObjectProperty.inverseImage IsZero F

end CategoryTheory
