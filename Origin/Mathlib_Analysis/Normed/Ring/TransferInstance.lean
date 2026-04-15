/-
Extracted from Analysis/Normed/Ring/TransferInstance.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Transfer normed algebraic structures across `Equiv`s

In this file, we transfer a (semi-)normed ring structure across an equivalence.
This continues the pattern set in `Mathlib/Algebra/Module/TransferInstance.lean`.
-/

variable {α β : Type*}

namespace Equiv

protected abbrev seminormedRing [SeminormedRing β] (e : α ≃ β) :
    SeminormedRing α :=
  letI := e.ring
  .induced α β e.ringEquiv

protected abbrev normedRing [NormedRing β] (e : α ≃ β) : NormedRing α :=
  letI := e.ring
  .induced α β e.ringEquiv e.injective

end Equiv
