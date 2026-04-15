/-
Extracted from SetTheory/Ordinal/Principal.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Principal ordinals

We define principal or indecomposable ordinals, and we prove the standard properties about them.

## Main definitions and results

* `IsPrincipal`: A principal or indecomposable ordinal under some binary operation. We include 0 and
  any other typically excluded edge cases for simplicity.
* `not_bddAbove_setOf_isPrincipal`: Principal ordinals (under any operation) are unbounded.
* `isPrincipal_add_iff_zero_or_omega0_opow`: The main characterization theorem for additive
  principal ordinals.
* `isPrincipal_mul_iff_le_two_or_omega0_opow_opow`: The main characterization theorem for
  multiplicative principal ordinals.

## TODO

* Prove that exponential principal ordinals are 0, 1, 2, ω, or epsilon numbers, i.e. fixed points
  of `fun x ↦ ω ^ x`.
-/

universe u

open Order

namespace Ordinal

variable {a b c o : Ordinal.{u}}

section Arbitrary

variable {op : Ordinal → Ordinal → Ordinal}

/-! ### Principal ordinals -/

def IsPrincipal (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) : Prop :=
  ∀ ⦃a b⦄, a < o → b < o → op a b < o
