/-
Extracted from Data/Nat/Prime/Nth.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Nth

noncomputable section

/-!
# The Nth primes
-/

namespace Nat

@[simp]
theorem nth_prime_zero_eq_two : nth Prime 0 = 2 := nth_count prime_two

alias zeroth_prime_eq_two := nth_prime_zero_eq_two

@[simp]
theorem nth_prime_one_eq_three : nth Nat.Prime 1 = 3 := nth_count prime_three

end Nat
