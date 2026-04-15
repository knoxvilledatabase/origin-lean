/-
Extracted from Analysis/Normed/Field/TransferInstance.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Transfer normed algebraic structures across `Equiv`s

In this file, we transfer a normed field structure across an equivalence.
This continues the pattern set in `Mathlib/Algebra/Module/TransferInstance.lean`.
-/

variable {α β : Type*}

namespace Equiv

protected abbrev normedField [NormedField β] (e : α ≃ β) : NormedField α :=
  letI := e.field
  .induced α β e.ringEquiv e.injective

end Equiv
