/-
Extracted from CategoryTheory/Square.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The category of commutative squares

In this file, we define a bundled version of `CommSq`
which allows to consider commutative squares as
objects in a category `Square C`.

The four objects in a commutative square are
numbered as follows:
```
X₁ --> X₂
|      |
v      v
X₃ --> X₄
```

We define the flip functor, and two equivalences with
the category `Arrow (Arrow C)`, depending on whether
we consider a commutative square as a horizontal
morphism between two vertical maps (`arrowArrowEquivalence`)
or a vertical morphism between two horizontal
maps (`arrowArrowEquivalence'`).

-/

universe v v' u u'

namespace CategoryTheory

open Category

variable (C : Type u) [Category.{v} C] {D : Type u'} [Category.{v'} D]

structure Square where
  /-- the top-left object -/
  {X₁ : C}
  /-- the top-right object -/
  {X₂ : C}
  /-- the bottom-left object -/
  {X₃ : C}
  /-- the bottom-right object -/
  {X₄ : C}
  /-- the top morphism -/
  f₁₂ : X₁ ⟶ X₂
  /-- the left morphism -/
  f₁₃ : X₁ ⟶ X₃
  /-- the right morphism -/
  f₂₄ : X₂ ⟶ X₄
  /-- the bottom morphism -/
  f₃₄ : X₃ ⟶ X₄
  fac : f₁₂ ≫ f₂₄ = f₁₃ ≫ f₃₄

namespace Square

variable {C}

lemma commSq (sq : Square C) : CommSq sq.f₁₂ sq.f₁₃ sq.f₂₄ sq.f₃₄ where
  w := sq.fac
