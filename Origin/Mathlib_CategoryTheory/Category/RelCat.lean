/-
Extracted from CategoryTheory/Category/RelCat.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Basics on the category of relations

We define the category of types `CategoryTheory.RelCat` with binary relations as morphisms.
Associating each function with the relation defined by its graph yields a faithful and
essentially surjective functor `graphFunctor` that also characterizes all isomorphisms
(see `rel_iso_iff`).

By flipping the arguments to a relation, we construct an equivalence `opEquivalence` between
`RelCat` and its opposite.
-/

open SetRel

namespace CategoryTheory

universe u

def RelCat :=
  Type u

deriving Inhabited

namespace RelCat

variable {X Y Z : RelCat.{u}}

structure Hom (X Y : RelCat.{u}) : Type u where
  /-- Build a morphism `X ⟶ Y` for `X Y : RelCat` from a relation between `X` and `Y`. -/
  ofRel ::
  /-- The underlying relation between `X` and `Y` of a morphism `X ⟶ Y` for `X Y : RelCat`. -/
  rel : SetRel X Y

initialize_simps_projections Hom (as_prefix rel)

-- INSTANCE (free from Core): instLargeCategory

namespace Hom
