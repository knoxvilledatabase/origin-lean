/-
Extracted from Analysis/SpecialFunctions/Pow/Complex.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # Power function on `ℂ`

We construct the power functions `x ^ y`, where `x` and `y` are complex numbers.
-/

open Real Topology Filter ComplexConjugate Finset Set

namespace Complex

noncomputable def cpow (x y : ℂ) : ℂ :=
  if x = 0 then if y = 0 then 1 else 0 else exp (log x * y)

-- INSTANCE (free from Core): :
