/-
Extracted from Analysis/SpecialFunctions/Log/ENNRealLog.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Extended Nonnegative Real Logarithm

We define `log` as an extension of the logarithm of a positive real
to the extended nonnegative reals `ℝ≥0∞`. The function takes values
in the extended reals `EReal`, with `log 0 = ⊥` and `log ⊤ = ⊤`.

## Main Definitions
- `ENNReal.log`: The extension of the real logarithm to `ℝ≥0∞`.

## Main Results
- `ENNReal.log_strictMono`: `log` is increasing;
- `ENNReal.log_injective`, `ENNReal.log_surjective`, `ENNReal.log_bijective`: `log` is
  injective, surjective, and bijective;
- `ENNReal.log_mul_add`, `ENNReal.log_pow`, `ENNReal.log_rpow`: `log` satisfies
  the identities `log (x * y) = log x + log y` and `log (x ^ y) = y * log x`
  (with either `y ∈ ℕ` or `y ∈ ℝ`).

## Tags
ENNReal, EReal, logarithm
-/

namespace ENNReal

open scoped NNReal

/-! ### Definition -/

section Definition

noncomputable def log (x : ℝ≥0∞) : EReal :=
  if x = 0 then ⊥
    else if x = ⊤ then ⊤
    else Real.log x.toReal
