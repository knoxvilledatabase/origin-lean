/-
Extracted from CategoryTheory/Comma/Basic.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Comma categories

A comma category is a construction in category theory, which builds a category out of two functors
with a common codomain. Specifically, for functors `L : A ⥤ T` and `R : B ⥤ T`, an object in
`Comma L R` is a morphism `hom : L.obj left ⟶ R.obj right` for some objects `left : A` and
`right : B`, and a morphism in `Comma L R` between `hom : L.obj left ⟶ R.obj right` and
`hom' : L.obj left' ⟶ R.obj right'` is a commutative square

```
L.obj left  ⟶  L.obj left'
      |               |
  hom |               | hom'
      ↓               ↓
R.obj right ⟶  R.obj right',
```

where the top and bottom morphism come from morphisms `left ⟶ left'` and `right ⟶ right'`,
respectively.

## Main definitions

* `Comma L R`: the comma category of the functors `L` and `R`.
* `Over X`: the over category of the object `X` (developed in `Over.lean`).
* `Under X`: the under category of the object `X` (also developed in `Over.lean`).
* `Arrow T`: the arrow category of the category `T` (developed in `Arrow.lean`).

## References

* <https://ncatlab.org/nlab/show/comma+category>

## Tags

comma, slice, coslice, over, under, arrow
-/

namespace CategoryTheory

open Category

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {A : Type u₁} [Category.{v₁} A]

variable {B : Type u₂} [Category.{v₂} B]

variable {T : Type u₃} [Category.{v₃} T]

variable {A' : Type u₄} [Category.{v₄} A']

variable {B' : Type u₅} [Category.{v₅} B']

variable {T' : Type u₆} [Category.{v₆} T']

structure Comma (L : A ⥤ T) (R : B ⥤ T) : Type max u₁ u₂ v₃ where
  /-- The left subobject -/
  left : A
  /-- The right subobject -/
  right : B
  /-- A morphism from `L.obj left` to `R.obj right` -/
  hom : L.obj left ⟶ R.obj right

-- INSTANCE (free from Core): Comma.inhabited

variable {L : A ⥤ T} {R : B ⥤ T}
