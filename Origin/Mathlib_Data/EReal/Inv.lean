/-
Extracted from Data/EReal/Inv.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Absolute value, sign, inversion and division on extended real numbers

This file defines an absolute value and sign function on `EReal` and uses them to provide a
`CommMonoidWithZero` instance, based on the absolute value and sign characterising all `EReal`s.
Then it defines the inverse of an `EReal` as `⊤⁻¹ = ⊥⁻¹ = 0`, which leads to a
`DivInvMonoid` instance and division.
-/

open ENNReal Set SignType

noncomputable section

namespace EReal

/-! ### Absolute value -/

protected def abs : EReal → ℝ≥0∞
  | ⊥ => ⊤
  | ⊤ => ⊤
  | (x : ℝ) => ENNReal.ofReal |x|
