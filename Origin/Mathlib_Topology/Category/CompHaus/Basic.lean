/-
Extracted from Topology/Category/CompHaus/Basic.lean
Genuine: 3 of 8 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# The category of Compact Hausdorff Spaces

We construct the category of compact Hausdorff spaces.
The type of compact Hausdorff spaces is denoted `CompHaus`, and it is endowed with a category
instance making it a full subcategory of `TopCat`.
The fully faithful functor `CompHaus ⥤ TopCat` is denoted `compHausToTop`.

**Note:** The file `Mathlib/Topology/Category/Compactum.lean` provides the equivalence between
`Compactum`, which is defined as the category of algebras for the ultrafilter monad, and `CompHaus`.
`CompactumToCompHaus` is the functor from `Compactum` to `CompHaus` which is proven to be an
equivalence of categories in `CompactumToCompHaus.isEquivalence`.
See `Mathlib/Topology/Category/Compactum.lean` for a more detailed discussion where these
definitions are introduced.

## Implementation

The category `CompHaus` is defined using the structure `CompHausLike`. See the file
`CompHausLike.Basic` for more information.

-/

universe v u

open CategoryTheory CompHausLike

abbrev CompHaus := CompHausLike (fun _ ↦ True)

namespace CompHaus

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {X

-- INSTANCE (free from Core): {X

variable (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]

-- INSTANCE (free from Core): :

abbrev of : CompHaus := CompHausLike.of _ X

end CompHaus

abbrev compHausToTop : CompHaus.{u} ⥤ TopCat.{u} :=
  CompHausLike.compHausLikeToTop _
