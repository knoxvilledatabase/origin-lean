/-
Extracted from Algebra/Group/ForwardDiff.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Forward difference operators and Newton series

We define the forward difference operator, sending `f` to the function `x ↦ f (x + h) - f x` for
a given `h` (for any additive semigroup, taking values in an abelian group). The notation `Δ_[h]` is
defined for this operator, scoped in namespace `fwdDiff`.

We prove two key formulae about this operator:

* `shift_eq_sum_fwdDiff_iter`: the **Gregory-Newton formula**, expressing `f (y + n • h)` as a
  linear combination of forward differences of `f` at `y`, for `n ∈ ℕ`;
* `fwdDiff_iter_eq_sum_shift`: formula expressing the `n`-th forward difference of `f` at `y` as
  a linear combination of `f (y + k • h)` for `0 ≤ k ≤ n`.

We also prove some auxiliary results about iterated forward differences of the function
`n ↦ n.choose k`.
-/

open Finset Nat Function Polynomial

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

def fwdDiff (h : M) (f : M → G) : M → G := fun n ↦ f (n + h) - f n
