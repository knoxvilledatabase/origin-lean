/-
Extracted from Analysis/SpecialFunctions/Log/ERealExp.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Extended Nonnegative Real Exponential

We define `exp` as an extension of the exponential of a real
to the extended reals `EReal`. The function takes values
in the extended nonnegative reals `ℝ≥0∞`, with `exp ⊥ = 0` and `exp ⊤ = ⊤`.

## Main Definitions
- `EReal.exp`: The extension of the real exponential to `EReal`.

## Main Results
- `EReal.exp_strictMono`: `exp` is increasing;
- `EReal.exp_neg`, `EReal.exp_add`: `exp` satisfies
  the identities `exp (-x) = (exp x)⁻¹` and `exp (x + y) = exp x * exp y`.

## Tags
ENNReal, EReal, exponential
-/

namespace EReal

open scoped ENNReal

/-! ### Definition -/

section Definition

noncomputable

def exp (x : EReal) : ℝ≥0∞ := EReal.rec 0 (fun x => ENNReal.ofReal (Real.exp x)) ∞ x
