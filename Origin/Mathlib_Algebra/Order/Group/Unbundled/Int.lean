/-
Extracted from Algebra/Order/Group/Unbundled/Int.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Facts about `ℤ` as an (unbundled) ordered group

See note [foundational algebra order theory].

## Recursors

* `Int.rec`: Sign disjunction. Something is true/defined on `ℤ` if it's true/defined for nonnegative
  and for negative values. (Defined in core Lean 3)
* `Int.inductionOn`: Simple growing induction on positive numbers, plus simple decreasing induction
  on negative numbers. Note that this recursor is currently only `Prop`-valued.
* `Int.inductionOn'`: Simple growing induction for numbers greater than `b`, plus simple decreasing
  induction on numbers less than `b`.
-/

assert_not_exists Set.Subsingleton Ring

open Function Nat

namespace Int

theorem natCast_strictMono : StrictMono (· : ℕ → ℤ) := fun _ _ ↦ Int.ofNat_lt.2

/-! ### Miscellaneous lemmas -/

theorem abs_eq_natAbs : ∀ a : ℤ, |a| = natAbs a
  | (n : ℕ) => abs_of_nonneg <| natCast_nonneg _
  | -[_+1] => abs_of_nonpos <| le_of_lt <| negSucc_lt_zero _
