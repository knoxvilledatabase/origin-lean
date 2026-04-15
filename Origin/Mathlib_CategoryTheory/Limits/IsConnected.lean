/-
Extracted from CategoryTheory/Limits/IsConnected.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Colimits of connected index categories

This file proves two characterizations of connected categories by means of colimits.

## Characterization of connected categories by means of the unit-valued functor

First, it is proved that a category `C` is connected if and only if `colim F` is a singleton,
where `F : C ⥤ Type w` and `F.obj _ = PUnit` (for arbitrary `w`).

See `isConnected_iff_colimit_constPUnitFunctor_iso_pUnit` for the proof of this characterization and
`constPUnitFunctor` for the definition of the constant functor used in the statement. A formulation
based on `IsColimit` instead of `colimit` is given in `isConnected_iff_isColimit_pUnitCocone`.

The `if` direction is also available directly in several formulations:
For connected index categories `C`, `PUnit.{w}` is a colimit of the `constPUnitFunctor`, where `w`
is arbitrary. See `instHasColimitConstPUnitFunctor`, `isColimitPUnitCocone` and
`colimitConstPUnitIsoPUnit`.

## Final functors preserve connectedness of categories (in both directions)

`isConnected_iff_of_final` proves that the domain of a final functor is connected if and only if
its codomain is connected.

## Tags

unit-valued, singleton, colimit
-/

universe w v u

namespace CategoryTheory

namespace Limits.Types

variable (C : Type u) [Category.{v} C]

def constPUnitFunctor : C ⥤ Type w := (Functor.const C).obj PUnit.{w + 1}
