/-
Extracted from Order/Category/NonemptyFinLinOrd.lean
Genuine: 3 of 8 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Nonempty finite linear orders

This defines `NonemptyFinLinOrd`, the category of nonempty finite linear
orders with monotone maps. This is the index category for simplicial objects.

Note: `NonemptyFinLinOrd` is *not* a subcategory of `FinBddDistLat` because its morphisms do not
preserve `⊥` and `⊤`.
-/

universe u v

open CategoryTheory CategoryTheory.Limits

structure NonemptyFinLinOrd extends LinOrd where
  [nonempty : Nonempty carrier]
  [fintype : Fintype carrier]

attribute [instance] NonemptyFinLinOrd.nonempty NonemptyFinLinOrd.fintype

namespace NonemptyFinLinOrd

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): (X

abbrev of (α : Type*) [Nonempty α] [Fintype α] [LinearOrder α] : NonemptyFinLinOrd where
  carrier := α

abbrev ofHom {X Y : Type u} [Nonempty X] [LinearOrder X] [Fintype X]
    [Nonempty Y] [LinearOrder Y] [Fintype Y] (f : X →o Y) :
    of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := NonemptyFinLinOrd) f
