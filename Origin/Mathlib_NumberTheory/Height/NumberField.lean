/-
Extracted from NumberTheory/Height/NumberField.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Heights over number fields

We provide an instance of `Height.AdmissibleAbsValues` for algebraic number fields
and set up some API.
-/

/-!
### Instance for number fields
-/

namespace NumberField

open Height

variable {K : Type*} [Field K] [NumberField K]

variable (K) in

noncomputable def multisetInfinitePlace : Multiset (AbsoluteValue K ℝ) :=
  .bind (.univ : Finset (InfinitePlace K)).val fun v ↦ .replicate v.mult v.val
