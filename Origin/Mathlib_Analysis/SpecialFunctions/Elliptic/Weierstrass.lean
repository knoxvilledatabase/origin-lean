/-
Extracted from Analysis/SpecialFunctions/Elliptic/Weierstrass.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Weierstrass `℘` functions

## Main definitions and results
- `PeriodPair.weierstrassP`: The Weierstrass `℘`-function associated to a pair of periods.
- `PeriodPair.hasSumLocallyUniformly_weierstrassP`:
  The summands of `℘` sums to `℘` locally uniformly.
- `PeriodPair.differentiableOn_weierstrassP`: `℘` is differentiable away from the lattice points.
- `PeriodPair.weierstrassP_add_coe`: The Weierstrass `℘`-function is periodic.
- `PeriodPair.weierstrassP_neg`: The Weierstrass `℘`-function is even.

- `PeriodPair.derivWeierstrassP`:
  The derivative of the Weierstrass `℘`-function associated to a pair of periods.
- `PeriodPair.hasSumLocallyUniformly_derivWeierstrassP`:
  The summands of `℘'` sums to `℘'` locally uniformly.
- `PeriodPair.differentiableOn_derivWeierstrassP`:
  `℘'` is differentiable away from the lattice points.
- `PeriodPair.derivWeierstrassP_add_coe`: `℘'` is periodic.
- `PeriodPair.weierstrassP_neg`: `℘'` is odd.
- `PeriodPair.deriv_weierstrassP`: `deriv ℘ = ℘'`. This is true globally because of junk values.
- `PeriodPair.analyticOnNhd_weierstrassP`: `℘` is analytic away from the lattice points.
- `PeriodPair.meromorphic_weierstrassP`: `℘` is meromorphic on the whole plane.
- `PeriodPair.order_weierstrassP`: `℘` has a pole of order 2 at each of the lattice points.
- `PeriodPair.derivWeierstrassP_sq` : `℘'(z)² = 4 ℘(z)³ - g₂ ℘(z) - g₃`

## tags

Weierstrass p-functions, Weierstrass p functions

-/

open Module Filter

open scoped Topology Nat

noncomputable section

structure PeriodPair : Type where
  /-- The first period in a `PeriodPair`. -/
  ω₁ : ℂ
  /-- The second period in a `PeriodPair`. -/
  ω₂ : ℂ
  indep : LinearIndependent ℝ ![ω₁, ω₂]

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M] (L : PeriodPair)

namespace PeriodPair

protected def basis : Basis (Fin 2) ℝ ℂ :=
  basisOfLinearIndependentOfCardEqFinrank L.indep (by simp)
