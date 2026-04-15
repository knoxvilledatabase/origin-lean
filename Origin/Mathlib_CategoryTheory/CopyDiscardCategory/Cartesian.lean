/-
Extracted from CategoryTheory/CopyDiscardCategory/Cartesian.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Cartesian Categories as Copy-Discard Categories

Every cartesian monoidal category is a copy-discard category where:
- Copy is the diagonal map
- Discard is the unique map to terminal

## Main results

* `CopyDiscardCategory` instance for cartesian monoidal categories
* All morphisms in cartesian categories are deterministic

## Tags

cartesian, copy-discard, comonoid, symmetric monoidal
-/

universe v u

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory ComonObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory.{v} C]

namespace CartesianCopyDiscard

abbrev instComonObjOfCartesian (X : C) : ComonObj X :=
  ((cartesianComon C).obj X).comon

attribute [local instance] instComonObjOfCartesian

variable [BraidedCategory C]

-- INSTANCE (free from Core): instIsCommComonObjOfCartesian

abbrev ofCartesianMonoidalCategory : CopyDiscardCategory C where

attribute [local instance] ofCartesianMonoidalCategory

-- INSTANCE (free from Core): instDeterministic

end CartesianCopyDiscard

end CategoryTheory
