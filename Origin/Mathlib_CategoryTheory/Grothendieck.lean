/-
Extracted from CategoryTheory/Grothendieck.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Grothendieck construction

Given a functor `F : C ⥤ Cat`, the objects of `Grothendieck F`
consist of dependent pairs `(b, f)`, where `b : C` and `f : F.obj b`,
and a morphism `(b, f) ⟶ (b', f')` is a pair `β : b ⟶ b'` in `C`, and
`φ : (F.map β).toFunctor.obj f ⟶ f'`

`Grothendieck.functor` makes the Grothendieck construction into a functor from the functor category
`C ⥤ Cat` to the over category `Over C` in the category of categories.

Categories such as `PresheafedSpace` are in fact examples of this construction,
and it may be interesting to try to generalize some of the development there.

## Implementation notes

Really we should treat `Cat` as a 2-category, and allow `F` to be a 2-functor.

There is also a closely related construction starting with `G : Cᵒᵖ ⥤ Cat`,
where morphisms consist again of `β : b ⟶ b'` and `φ : f ⟶ (G.map (op β)).obj f'`.

## Notable constructions

- `Grothendieck F` is the Grothendieck construction.
- Elements of `Grothendieck F` whose base is `c : C` can be transported along `f : c ⟶ d` using
  `transport`.
- A natural transformation `α : F ⟶ G` induces `map α : Grothendieck F ⥤ Grothendieck G`.
- The Grothendieck construction and `map` together form a functor (`functor`) from the functor
  category `E ⥤ Cat` to the over category `Over E`.
- A functor `G : D ⥤ C` induces `pre F G : Grothendieck (G ⋙ F) ⥤ Grothendieck F`.

## References

See also `CategoryTheory.Functor.Elements` for the category of elements of a functor `F : C ⥤ Type`.

* https://stacks.math.columbia.edu/tag/02XV
* https://ncatlab.org/nlab/show/Grothendieck+construction

-/

universe w u v u₁ v₁ u₂ v₂

namespace CategoryTheory

open Functor

variable {C : Type u} [Category.{v} C]

variable {D : Type u₁} [Category.{v₁} D]

variable (F : C ⥤ Cat.{v₂, u₂})

structure Grothendieck where
  /-- The underlying object in `C` -/
  base : C
  /-- The object in the fiber of the base object. -/
  fiber : F.obj base

namespace Grothendieck

variable {F}

structure Hom (X Y : Grothendieck F) where
  /-- The morphism between base objects. -/
  base : X.base ⟶ Y.base
  /-- The morphism from the pushforward to the source fiber object to the target fiber object. -/
  fiber : (F.map base).toFunctor.obj X.fiber ⟶ Y.fiber
