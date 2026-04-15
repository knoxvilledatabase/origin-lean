/-
Extracted from RingTheory/PowerSeries/Expand.lean
Genuine: 4 of 6 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
## Expand power series

Given a power series `φ`, one may replace every occurrence of `X i` by `X i ^ n`,
for some nonzero natural number `n`.
This operation is called `PowerSeries.expand` and it is an algebra homomorphism.

### Main declaration

* `PowerSeries.expand`: expand a power series by a nonzero factor of p,
  so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.
-/

namespace PowerSeries

variable {τ R S : Type*} [CommRing R] [CommRing S] (p : ℕ) (hp : p ≠ 0)

noncomputable def expand : PowerSeries R →ₐ[R] PowerSeries R :=
  MvPowerSeries.expand p hp

theorem expand_apply (f : PowerSeries R) : expand p hp f = subst (X ^ p) f := by
  simp [expand, MvPowerSeries.expand, subst, X]

theorem expand_C (r : R) : expand p hp (C r : PowerSeries R) = C r := by
  conv_lhs => rw [← mul_one (C r), ← smul_eq_C_mul, expand, AlgHom.map_smul_of_tower,
    map_one, smul_eq_C_mul, mul_one]

-- DISSOLVED: expand_mul_eq_comp

-- DISSOLVED: expand_mul

theorem expand_smul (a : R) (φ : PowerSeries R) :
    expand p hp (a • φ) = a • φ.expand p hp := AlgHom.map_smul_of_tower _ _ _
