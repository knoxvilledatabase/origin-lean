/-
Extracted from Probability/ProbabilityMassFunction/Monad.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Monad Operations for Probability Mass Functions

This file constructs two operations on `PMF` that give it a monad structure.
`pure a` is the distribution where a single value `a` has probability `1`.
`bind pa pb : PMF β` is the distribution given by sampling `a : α` from `pa : PMF α`,
and then sampling from `pb a : PMF β` to get a final result `b : β`.

`bindOnSupport` generalizes `bind` to allow binding to a partial function,
so that the second argument only needs to be defined on the support of the first argument.

-/

noncomputable section

variable {α β γ : Type*}

open NNReal ENNReal

open MeasureTheory

namespace PMF

section Pure

open scoped Classical in

def pure (a : α) : PMF α :=
  ⟨fun a' => if a' = a then 1 else 0, hasSum_ite_eq _ _⟩

variable (a a' : α)

open scoped Classical in
