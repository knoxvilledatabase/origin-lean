/-
Extracted from CategoryTheory/Monad/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Monads

We construct the categories of monads and comonads, and their forgetful functors to endofunctors.

(Note that these are the category theorist's monads, not the programmers monads.
For the translation, see the file `Mathlib/CategoryTheory/Monad/Types.lean`.)

For the fact that monads are "just" monoids in the category of endofunctors, see the file
`CategoryTheory.Monad.EquivMon`.
-/

namespace CategoryTheory

open Category

universe v₁ u₁

variable (C : Type u₁) [Category.{v₁} C]

structure Monad extends C ⥤ C where
  /-- The unit for the monad. -/
  η : 𝟭 _ ⟶ toFunctor
  /-- The multiplication for the monad. -/
  μ : toFunctor ⋙ toFunctor ⟶ toFunctor
  assoc : ∀ X, toFunctor.map (NatTrans.app μ X) ≫ μ.app _ = μ.app _ ≫ μ.app _ := by cat_disch
  left_unit : ∀ X : C, η.app (toFunctor.obj X) ≫ μ.app _ = 𝟙 _ := by cat_disch
  right_unit : ∀ X : C, toFunctor.map (η.app X) ≫ μ.app _ = 𝟙 _ := by cat_disch
