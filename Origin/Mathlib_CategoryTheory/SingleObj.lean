/-
Extracted from CategoryTheory/SingleObj.lean
Genuine: 1 of 6 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Single-object category

Single object category with a given monoid of endomorphisms.
It is defined to facilitate transferring some definitions and lemmas (e.g., conjugacy etc.)
from category theory to monoids and groups.

## Main definitions

Given a type `M` with a monoid structure, `SingleObj M` is `Unit` type with `Category` structure
such that `End (SingleObj M).star` is the monoid `M`.  This can be extended to a functor
`MonCat ⥤ Cat`.

If `M` is a group, then `SingleObj M` is a groupoid.

An element `x : M` can be reinterpreted as an element of `End (SingleObj.star M)` using
`SingleObj.toEnd`.

## Implementation notes

- `categoryStruct.comp` on `End (SingleObj.star M)` is `flip (*)`, not `(*)`. This way
  multiplication on `End` agrees with the multiplication on `M`.

- By default, Lean puts instances into `CategoryTheory` namespace instead of
  `CategoryTheory.SingleObj`, so we give all names explicitly.
-/

assert_not_exists MonoidWithZero

universe u v w

namespace CategoryTheory

abbrev SingleObj :=
  Quiver.SingleObj

namespace SingleObj

variable (M G : Type u)

-- INSTANCE (free from Core): categoryStruct

variable [Monoid M] [Group G]

-- INSTANCE (free from Core): category

-- INSTANCE (free from Core): finCategoryOfFintype
