/-
Extracted from AlgebraicTopology/SimplicialSet/Monoidal.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 10
-/
import Origin.Core
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.CategoryTheory.ChosenFiniteProducts.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Types.Basic

noncomputable section

/-!
# The monoidal category structure on simplicial sets

This file defines an instance of chosen finite products
for the category `SSet`. It follows from the fact
the `SSet` if a category of functors to the category
of types and that the category of types have chosen
finite products. As a result, we obtain a monoidal
category structure on `SSet`.

-/

universe u

open Simplicial CategoryTheory MonoidalCategory

namespace SSet

noncomputable instance : ChosenFiniteProducts SSet.{u} :=
  (inferInstance : ChosenFiniteProducts (SimplexCategoryᵒᵖ ⥤ Type u))

end SSet
