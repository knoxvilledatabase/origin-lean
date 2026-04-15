/-
Extracted from RingTheory/RootsOfUnity/Complex.lean
Genuine: 1 of 13 | Dissolved: 12 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Complex roots of unity

In this file we show that the `n`-th complex roots of unity
are exactly the complex numbers `exp (2 * π * I * (i / n))` for `i ∈ Finset.range n`.

## Main declarations

* `Complex.mem_rootsOfUnity`: the complex `n`-th roots of unity are exactly the
  complex numbers of the form `exp (2 * π * I * (i / n))` for some `i < n`.
* `Complex.card_rootsOfUnity`: the number of `n`-th roots of unity is exactly `n`.
* `Complex.norm_rootOfUnity_eq_one`: A complex root of unity has norm `1`.

-/

namespace Complex

open Polynomial Real

open scoped Nat Real

-- DISSOLVED: isPrimitiveRoot_exp_of_coprime

-- DISSOLVED: isPrimitiveRoot_exp

-- DISSOLVED: isPrimitiveRoot_iff

-- DISSOLVED: mem_rootsOfUnity

-- DISSOLVED: card_rootsOfUnity

theorem card_primitiveRoots (k : ℕ) : (primitiveRoots k ℂ).card = φ k := by
  by_cases h : k = 0
  · simp [h]
  exact (isPrimitiveRoot_exp k h).card_primitiveRoots

end Complex

-- DISSOLVED: IsPrimitiveRoot.norm'_eq_one

-- DISSOLVED: IsPrimitiveRoot.nnnorm_eq_one

-- DISSOLVED: IsPrimitiveRoot.arg_ext

-- DISSOLVED: IsPrimitiveRoot.arg_eq_zero_iff

-- DISSOLVED: IsPrimitiveRoot.arg_eq_pi_iff

-- DISSOLVED: IsPrimitiveRoot.arg

-- DISSOLVED: Complex.norm_eq_one_of_mem_rootsOfUnity
