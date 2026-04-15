/-
Extracted from Data/Nat/Choose/Central.lean
Genuine: 2 of 4 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core

/-!
# Central binomial coefficients

This file proves properties of the central binomial coefficients (that is, `Nat.choose (2 * n) n`).

## Main definition and results

* `Nat.centralBinom`: the central binomial coefficient, `(2 * n).choose n`.
* `Nat.succ_mul_centralBinom_succ`: the inductive relationship between successive central binomial
  coefficients.
* `Nat.four_pow_lt_mul_centralBinom`: an exponential lower bound on the central binomial
  coefficient.
* `succ_dvd_centralBinom`: The result that `n+1 ∣ n.centralBinom`, ensuring that the explicit
  definition of the Catalan numbers is integer-valued.
-/

namespace Nat

def centralBinom (n : ℕ) :=
  (2 * n).choose n

theorem centralBinom_pos (n : ℕ) : 0 < centralBinom n :=
  choose_pos (Nat.le_mul_of_pos_left _ zero_lt_two)

-- DISSOLVED: centralBinom_ne_zero
