/-
Extracted from CategoryTheory/FintypeCat.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# The category of finite types.

We define the category of finite types, denoted `FintypeCat` as
the full subcategory of types with a `Finite` instance.

We also define `FintypeCat.Skeleton`, the standard skeleton of `FintypeCat` whose objects
are `Fin n` for `n : ℕ`. We prove that the obvious inclusion functor
`FintypeCat.Skeleton ⥤ FintypeCat` is an equivalence of categories in
`FintypeCat.Skeleton.equivalence`.
We prove that `FintypeCat.Skeleton` is a skeleton of `FintypeCat` in `FintypeCat.isSkeleton`.
-/

open CategoryTheory

abbrev FintypeCat := ObjectProperty.FullSubcategory (C := Type*) Finite

namespace FintypeCat

abbrev of (X : Type*) [Finite X] : FintypeCat :=
  ⟨X, inferInstance⟩

-- INSTANCE (free from Core): instCoeSort

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {X
