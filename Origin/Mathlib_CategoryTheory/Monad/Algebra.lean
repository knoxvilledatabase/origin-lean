/-
Extracted from CategoryTheory/Monad/Algebra.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Eilenberg-Moore (co)algebras for a (co)monad

This file defines Eilenberg-Moore (co)algebras for a (co)monad,
and provides the category instance for them.

Further it defines the adjoint pair of free and forgetful functors, respectively
from and to the original category, as well as the adjoint pair of forgetful and
cofree functors, respectively from and to the original category.

## References
* [Riehl, *Category theory in context*, Section 5.2.4][riehl2017]
-/

namespace CategoryTheory

open Category

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C]

namespace Monad

structure Algebra (T : Monad C) : Type max u₁ v₁ where
  /-- The underlying object associated to an algebra. -/
  A : C
  /-- The structure morphism associated to an algebra. -/
  a : (T : C ⥤ C).obj A ⟶ A
  /-- The unit axiom associated to an algebra. -/
  unit : T.η.app A ≫ a = 𝟙 A := by cat_disch
  /-- The associativity axiom associated to an algebra. -/
  assoc : T.μ.app A ≫ a = (T : C ⥤ C).map a ≫ a := by cat_disch

attribute [reassoc] Algebra.unit Algebra.assoc

namespace Algebra

variable {T : Monad C}
