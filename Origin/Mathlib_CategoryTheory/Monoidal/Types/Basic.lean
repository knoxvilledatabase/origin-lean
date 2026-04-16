/-
Extracted from CategoryTheory/Monoidal/Types/Basic.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 16
-/
import Origin.Core
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Types

noncomputable section

/-!
# The category of types is a monoidal category
-/

open CategoryTheory Limits MonoidalCategory

open Tactic

universe v u

namespace CategoryTheory

instance typesChosenFiniteProducts : ChosenFiniteProducts (Type u) where
  product := Types.binaryProductLimitCone
  terminal := Types.terminalLimitCone

noncomputable def MonoidalFunctor.mapPi {C : Type*} [Category C] [MonoidalCategory C]
    (F : Type _ ⥤ C) [F.Monoidal] (n : ℕ) (β : Type*) :
    F.obj (Fin (n + 1) → β) ≅ F.obj β ⊗ F.obj (Fin n → β) :=
  Functor.mapIso _ (Fin.consEquiv _).symm.toIso ≪≫ (Functor.Monoidal.μIso F β (Fin n → β)).symm

end CategoryTheory
