/-
Extracted from CategoryTheory/ObjectProperty/ColimitsCardinalClosure.lean
Genuine: 4 of 8 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Closure of a property of objects under colimits of bounded cardinality

In this file, given `P : ObjectProperty C` and `κ : Cardinal.{w}`,
we introduce the closure `P.colimitsCardinalClosure κ`
of `P` under colimits of shapes given by categories `J` such
that `Arrow J` is of cardinality `< κ`.

If `C` is locally `w`-small and `P` is essentially `w`-small,
we show that this closure `P.colimitsCardinalClosure κ` is
also essentially `w`-small.

-/

universe w v' v u' u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C) (κ : Cardinal.{w})

def colimitsCardinalClosure : ObjectProperty C :=
  P.colimitsClosure (SmallCategoryCardinalLT.categoryFamily κ)

lemma le_colimitsCardinalClosure : P ≤ P.colimitsCardinalClosure κ :=
  P.le_colimitsClosure _

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): [ObjectProperty.EssentiallySmall.{w}

-- INSTANCE (free from Core): (S

lemma isClosedUnderColimitsOfShape_colimitsCardinalClosure
    (J : Type u') [Category.{v'} J] (hJ : HasCardinalLT (Arrow J) κ) :
    (P.colimitsCardinalClosure κ).IsClosedUnderColimitsOfShape J := by
  obtain ⟨S, ⟨e⟩⟩ := SmallCategoryCardinalLT.exists_equivalence κ J hJ
  rw [isClosedUnderColimitsOfShape_iff_of_equivalence _ e.symm]
  infer_instance

lemma colimitsCardinalClosure_le {Q : ObjectProperty C} [Q.IsClosedUnderIsomorphisms]
    (hQ : ∀ (J : Type w) [SmallCategory J] (_ : HasCardinalLT (Arrow J) κ),
      Q.IsClosedUnderColimitsOfShape J) (h : P ≤ Q) :
    P.colimitsCardinalClosure κ ≤ Q := by
  have (i : SmallCategoryCardinalLT κ) := hQ _ i.hasCardinalLT
  exact colimitsClosure_le h

open Limits

-- INSTANCE (free from Core): isStableUnderRetracts_colimitsCardinalClosure

end

end CategoryTheory.ObjectProperty
