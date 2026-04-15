/-
Extracted from Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Real powers defined via the continuous functional calculus

This file defines real powers via the continuous functional calculus (CFC) and builds its API.
This allows one to take real powers of matrices, operators, elements of a C⋆-algebra, etc. The
square root is also defined via the non-unital CFC.

## Main declarations

+ `CFC.nnrpow`: the `ℝ≥0` power function based on the non-unital CFC, i.e. `cfcₙ NNReal.rpow`
  composed with `(↑) : ℝ≥0 → ℝ`.
+ `CFC.sqrt`: the square root function based on the non-unital CFC, i.e. `cfcₙ NNReal.sqrt`
+ `CFC.rpow`: the real power function based on the unital CFC, i.e. `cfc NNReal.rpow`

## Implementation notes

We define two separate versions `CFC.nnrpow` and `CFC.rpow` due to what happens at 0. Since
`NNReal.rpow 0 0 = 1`, this means that this function does not map zero to zero when the exponent
is zero, and hence `CFC.nnrpow a 0 = 0` whereas `CFC.rpow a 0 = 1`. Note that the non-unital version
only makes sense for nonnegative exponents, and hence we define it such that the exponent is in
`ℝ≥0`.

## Notation

+ We define a `Pow A ℝ` instance for `CFC.rpow`, i.e `a ^ y` with `A` an operator and `y : ℝ` works
  as expected. Likewise, we define a `Pow A ℝ≥0` instance for `CFC.nnrpow`. Note that these are
  low-priority instances, in order to avoid overriding instances such as `Pow ℝ ℝ`,
  `Pow (A × B) ℝ` or `Pow (∀ i, A i) ℝ`.

## TODO

+ Relate these to the log and exp functions
+ Lemmas about how these functions interact with commuting `a` and `b`.
+ Prove the order properties (operator monotonicity and concavity/convexity)
-/

open scoped NNReal

namespace NNReal

noncomputable abbrev nnrpow (a : ℝ≥0) (b : ℝ≥0) : ℝ≥0 := a ^ (b : ℝ)
