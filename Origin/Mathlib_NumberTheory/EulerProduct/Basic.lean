/-
Extracted from NumberTheory/EulerProduct/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Euler Products

The main result in this file is `EulerProduct.eulerProduct_hasProd`, which says that
if `f : ℕ → R` is norm-summable, where `R` is a complete normed commutative ring and `f` is
multiplicative on coprime arguments with `f 0 = 0`, then
`∏' p : Primes, ∑' e : ℕ, f (p^e)` converges to `∑' n, f n`.

`ArithmeticFunction.IsMultiplicative.eulerProduct_hasProd` is a version
for multiplicative arithmetic functions in the sense of
`ArithmeticFunction.IsMultiplicative`.

There is also a version `EulerProduct.eulerProduct_completely_multiplicative_hasProd`,
which states that `∏' p : Primes, (1 - f p)⁻¹` converges to `∑' n, f n`
when `f` is completely multiplicative with values in a complete normed field `F`
(implemented as `f : ℕ →*₀ F`).

There are variants stating the equality of the infinite product and the infinite sum
(`EulerProduct.eulerProduct_tprod`, `ArithmeticFunction.IsMultiplicative.eulerProduct_tprod`,
`EulerProduct.eulerProduct_completely_multiplicative_tprod`) and also variants stating
the convergence of the sequence of partial products over primes `< n`
(`EulerProduct.eulerProduct`, `ArithmeticFunction.IsMultiplicative.eulerProduct`,
`EulerProduct.eulerProduct_completely_multiplicative`.)

An intermediate step is `EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum`
(and its variant `EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric`),
which relates the finite product over primes `p ∈ s` to the sum of `f n` over `s`-factored `n`,
for `s : Finset ℕ`.

## Tags

Euler product, multiplicative function
-/

lemma Summable.norm_lt_one {F : Type*} [NormedDivisionRing F] [CompleteSpace F] {f : ℕ →* F}
    (hsum : Summable f) {p : ℕ} (hp : 1 < p) :
    ‖f p‖ < 1 := by
  refine summable_geometric_iff_norm_lt_one.mp ?_
  simp_rw [← map_pow]
  exact hsum.comp_injective <| Nat.pow_right_injective hp

open scoped Topology

open Nat Finset

section General

/-!
### General Euler Products

In this section we consider multiplicative (on coprime arguments) functions `f : ℕ → R`,
where `R` is a complete normed commutative ring. The main result is `EulerProduct.eulerProduct`.
-/

variable {R : Type*} [NormedCommRing R] {f : ℕ → R}
