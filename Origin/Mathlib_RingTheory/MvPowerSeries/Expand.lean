/-
Extracted from RingTheory/MvPowerSeries/Expand.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
## Expand multivariate power series

Given a multivariate power series `φ`, one may replace every occurrence of `X i` by `X i ^ n`,
for some nonzero natural number `n`.
This operation is called `MvPowerSeries.expand` and it is an algebra homomorphism.

### Main declaration

* `MvPowerSeries.expand`: expand a multi variate power series by a nonzero factor of p,
  so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.
-/

namespace MvPowerSeries

variable {σ τ R S : Type*} [CommRing R] [CommRing S] (p : ℕ) (hp : p ≠ 0)

noncomputable def expand : MvPowerSeries σ R →ₐ[R] MvPowerSeries σ R :=
  substAlgHom (HasSubst.X_pow hp)

theorem expand_C (r : R) : expand p hp (C r : MvPowerSeries σ R) = C r := by
  conv_lhs => rw [← mul_one (C r), ← smul_eq_C_mul, expand, AlgHom.map_smul_of_tower,
    map_one, smul_eq_C_mul, mul_one]
