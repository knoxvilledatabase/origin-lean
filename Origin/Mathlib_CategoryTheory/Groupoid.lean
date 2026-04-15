/-
Extracted from CategoryTheory/Groupoid.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Groupoids

We define `Groupoid` as a typeclass extending `Category`,
asserting that all morphisms have inverses.

The instance `IsIso.ofGroupoid (f : X ⟶ Y) : IsIso f` means that you can then write
`inv f` to access the inverse of any morphism `f`.

`Groupoid.isoEquivHom : (X ≅ Y) ≃ (X ⟶ Y)` provides the equivalence between
isomorphisms and morphisms in a groupoid.

We provide a (non-instance) constructor `Groupoid.ofIsIso` from an existing category
with `IsIso f` for every `f`.

## See also

See also `CategoryTheory.Core` for the groupoid of isomorphisms in a category.
-/

namespace CategoryTheory

universe v v₂ u u₂

class Groupoid (obj : Type u) : Type max u (v + 1) extends Category.{v} obj where
  /-- The inverse morphism -/
  inv : ∀ {X Y : obj}, (X ⟶ Y) → (Y ⟶ X)
  /-- `inv f` composed `f` is the identity -/
  inv_comp : ∀ {X Y : obj} (f : X ⟶ Y), comp (inv f) f = id Y := by cat_disch
  /-- `f` composed with `inv f` is the identity -/
  comp_inv : ∀ {X Y : obj} (f : X ⟶ Y), comp f (inv f) = id X := by cat_disch

initialize_simps_projections Groupoid (-Hom)

abbrev LargeGroupoid (C : Type (u + 1)) : Type (u + 1) :=
  Groupoid.{u} C

abbrev SmallGroupoid (C : Type u) : Type (u + 1) :=
  Groupoid.{u} C

variable {C : Type u} [Groupoid.{v} C] {X Y : C}

-- INSTANCE (free from Core): (priority
