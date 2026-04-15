/-
Extracted from CategoryTheory/ObjectProperty/FunctorCategory/PreservesLimits.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Preservation of limits, as a property of objects in the functor category

We make the typeclass `PreservesLimitsOfShape K` (resp. `PreservesFiniteLimits`)
a property of objects in the functor category `J ⥤ C`, and show that
it is stable under colimits of shape `K'` when they
commute to limits of shape `K` (resp. to finite limits).

-/

namespace CategoryTheory

open Limits

variable {J J' C D : Type*} (K K' : Type*)
  [Category* K] [Category* K'] [Category* J] [Category* J'] [Category* C] [Category* D]

namespace ObjectProperty

variable {K} in

abbrev preservesLimit (F : K ⥤ J) : ObjectProperty (J ⥤ C) := PreservesLimit F
