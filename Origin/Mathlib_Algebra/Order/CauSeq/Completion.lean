/-
Extracted from Algebra/Order/CauSeq/Completion.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cauchy completion

This file generalizes the Cauchy completion of `(ℚ, abs)` to the completion of a ring
with absolute value.
-/

namespace CauSeq.Completion

open CauSeq

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] (abv : β → α) [IsAbsoluteValue abv]

def Cauchy :=
  @Quotient (CauSeq _ abv) CauSeq.equiv

variable {abv}

def mk : CauSeq _ abv → Cauchy abv :=
  Quotient.mk''
