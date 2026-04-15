/-
Extracted from NumberTheory/Chebyshev.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Chebyshev functions

This file defines the Chebyshev functions `theta` and `psi`.
These give logarithmically weighted sums of primes and prime powers.

## Main definitions

- `Chebyshev.psi` gives the sum of `ArithmeticFunction.vonMangoldt`
- `Chebyshev.theta` gives the sum of `log p` over primes

## Main results

- `Chebyshev.theta_eq_log_primorial` shows that `θ x` is the log of the product of primes up to x
- `Chebyshev.theta_le_log4_mul_x` gives Chebyshev's upper bound on `θ`
- `Chebyshev.psi_eq_sum_theta` and `Chebyshev.psi_eq_theta_add_sum_theta` relate `psi` to `theta`.
- `Chebyshev.psi_le_const_mul_self` gives Chebyshev's upper bound on `ψ`.
- `Chebyshev.primeCounting_eq_theta_div_log_add_integral` relates the prime counting function to `θ`
- `Chebyshev.eventually_primeCounting_le` gives an upper bound on the prime counting function.

## Notation

We introduce the scoped notations `θ` and `ψ` in the Chebyshev namespace for the Chebyshev
functions.

## References

Parts of this file were upstreamed from the PrimeNumberTheoremAnd project by Kontorovich et al, https://github.com/alexKontorovich/PrimeNumberTheoremAnd.

## TODOS

- Prove Chebyshev's lower bound.
-/

open Nat hiding log

open Finset Real

open ArithmeticFunction hiding log

open scoped Nat.Prime

namespace Chebyshev

noncomputable def psi (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n
