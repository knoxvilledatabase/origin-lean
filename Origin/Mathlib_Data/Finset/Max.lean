/-
Extracted from Data/Finset/Max.lean
Genuine: 1 of 3 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core

/-!
# Maximum and minimum of finite sets
-/

assert_not_exists IsOrderedMonoid MonoidWithZero

open Function Multiset OrderDual

variable {F α β γ ι κ : Type*}

namespace Finset

/-! ### max and min of finite sets -/

section MaxMin

variable [LinearOrder α]

protected def max (s : Finset α) : WithBot α :=
  sup s (↑)

-- DISSOLVED: max_eq_sup_withBot
