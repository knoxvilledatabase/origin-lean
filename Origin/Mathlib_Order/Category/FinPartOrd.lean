/-
Extracted from Order/Category/FinPartOrd.lean
Genuine: 3 of 10 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

/-!
# The category of finite partial orders

This defines `FinPartOrd`, the category of finite partial orders.

Note: `FinPartOrd` is *not* a subcategory of `BddOrd` because finite orders are not necessarily
bounded.

## TODO

`FinPartOrd` is equivalent to a small category.
-/

universe u v

open CategoryTheory

structure FinPartOrd extends PartOrd where
  [isFintype : Fintype toPartOrd]

namespace FinPartOrd

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): (X

attribute [instance] FinPartOrd.isFintype

abbrev of (α : Type*) [PartialOrder α] [Fintype α] : FinPartOrd where
  carrier := α

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): largeCategory

-- INSTANCE (free from Core): concreteCategory

-- INSTANCE (free from Core): hasForgetToPartOrd

-- INSTANCE (free from Core): hasForgetToFintype

abbrev ofHom {X Y : Type u} [PartialOrder X] [Fintype X] [PartialOrder Y] [Fintype Y] (f : X →o Y) :
    of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := FinPartOrd) f
