/-
Extracted from Topology/Category/CompactlyGenerated.lean
Genuine: 3 of 7 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!

# Compactly generated topological spaces

This file defines the category of compactly generated topological spaces. These are spaces `X` such
that a map `f : X → Y` is continuous whenever the composition `S → X → Y` is continuous for all
compact Hausdorff spaces `S` mapping continuously to `X`.

## TODO

* `CompactlyGenerated` is a reflective subcategory of `TopCat`.
* `CompactlyGenerated` is Cartesian closed.
* Every first-countable space is `u`-compactly generated for every universe `u`.
-/

universe u w

open CategoryTheory Topology TopologicalSpace

structure CompactlyGenerated where
  /-- The underlying topological space of an object of `CompactlyGenerated`. -/
  toTop : TopCat.{w}
  /-- The underlying topological space is compactly generated. -/
  [is_compactly_generated : UCompactlyGeneratedSpace.{u} toTop]

namespace CompactlyGenerated

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

attribute [instance] is_compactly_generated

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable (X : Type w) [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X]

abbrev of : CompactlyGenerated.{u, w} where
  toTop := TopCat.of X
  is_compactly_generated := ‹_›

variable {X} {Y : Type w} [TopologicalSpace Y] [UCompactlyGeneratedSpace.{u} Y]

abbrev ofHom (f : C(X, Y)) : of X ⟶ of Y := ConcreteCategory.ofHom f

end
