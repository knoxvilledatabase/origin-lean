/-
Extracted from Analysis/Normed/Field/UnitBall.lean
Genuine: 1 of 5 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Algebraic structures on unit balls and spheres

In this file we define algebraic structures (`Semigroup`, `CommSemigroup`, `Monoid`, `CommMonoid`,
`Group`, `CommGroup`) on `Metric.ball (0 : 𝕜) 1`, `Metric.closedBall (0 : 𝕜) 1`, and
`Metric.sphere (0 : 𝕜) 1`. In each case we use the weakest possible typeclass assumption on `𝕜`,
from `NonUnitalSeminormedRing` to `NormedField`.
-/

open Set Metric

variable {𝕜 : Type*}

/-!
### Algebraic structures on `Metric.ball 0 1`
-/

def Subsemigroup.unitBall (𝕜 : Type*) [NonUnitalSeminormedRing 𝕜] : Subsemigroup 𝕜 where
  carrier := ball (0 : 𝕜) 1
  mul_mem' hx hy := by
    rw [mem_ball_zero_iff] at *
    exact (norm_mul_le _ _).trans_lt (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx hy.le)

-- INSTANCE (free from Core): Metric.unitBall.instSemigroup

-- INSTANCE (free from Core): Metric.unitBall.instContinuousMul

-- INSTANCE (free from Core): Metric.unitBall.instCommSemigroup

-- INSTANCE (free from Core): Metric.unitBall.instHasDistribNeg
