/-
Extracted from Order/Category/Semilat.lean
Genuine: 2 of 8 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# The categories of semilattices

This defines `SemilatSupCat` and `SemilatInfCat`, the categories of sup-semilattices with a bottom
element and inf-semilattices with a top element.

## References

* [nLab, *semilattice*](https://ncatlab.org/nlab/show/semilattice)
-/

universe u

open CategoryTheory

structure SemilatSupCat : Type (u + 1) where
  /-- Construct a bundled `SemilatSupCat` from a `SemilatticeSup`. -/
  of ::
  /-- The underlying type of a sup-semilattice with a bottom element. -/
  protected X : Type u
  [isSemilatticeSup : SemilatticeSup X]
  [isOrderBot : OrderBot.{u} X]

structure SemilatInfCat : Type (u + 1) where
  /-- Construct a bundled `SemilatInfCat` from a `SemilatticeInf`. -/
  of ::
  /-- The underlying type of an inf-semilattice with a top element. -/
  protected X : Type u
  [isSemilatticeInf : SemilatticeInf X]
  [isOrderTop : OrderTop.{u} X]

namespace SemilatSupCat

-- INSTANCE (free from Core): :

attribute [instance] isSemilatticeSup isOrderBot

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): hasForgetToPartOrd
