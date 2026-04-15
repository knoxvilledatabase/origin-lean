/-
Extracted from CategoryTheory/Endofunctor/Algebra.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Algebras of endofunctors

This file defines (co)algebras of an endofunctor, and provides the category instance for them.
It also defines the forgetful functor from the category of (co)algebras. It is shown that the
structure map of the initial algebra of an endofunctor is an isomorphism. Furthermore, it is shown
that for an adjunction `F ⊣ G` the category of algebras over `F` is equivalent to the category of
coalgebras over `G`.

## TODO

* Prove that if the countable infinite product over the powers of the endofunctor exists, then
  algebras over the endofunctor coincide with algebras over the free monad on the endofunctor.
-/

universe v u

namespace CategoryTheory

namespace Endofunctor

variable {C : Type u} [Category.{v} C]

structure Algebra (F : C ⥤ C) where
  /-- carrier of the algebra -/
  a : C
  /-- structure morphism of the algebra -/
  str : F.obj a ⟶ a

-- INSTANCE (free from Core): [Inhabited

namespace Algebra

variable {F : C ⥤ C} (A : Algebra F) {A₀ A₁ A₂ : Algebra F}
