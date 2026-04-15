/-
Extracted from Analysis/Normed/Module/Ball/Action.lean
Genuine: 1 of 34 | Dissolved: 1 | Infrastructure: 32
-/
import Origin.Core

/-!
# Multiplicative actions of/on balls and spheres

Let `E` be a normed vector space over a normed field `𝕜`. In this file we define the following
multiplicative actions.

- The closed unit ball in `𝕜` acts on open balls and closed balls centered at `0` in `E`.
- The unit sphere in `𝕜` acts on open balls, closed balls, and spheres centered at `0` in `E`.
-/

open Metric Set

variable {𝕜 𝕜' E : Type*} [NormedField 𝕜] [NormedField 𝕜'] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] {r : ℝ}

section ClosedBall

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): mulActionClosedBallBall

-- INSTANCE (free from Core): continuousSMul_closedBall_ball

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): mulActionClosedBallClosedBall

-- INSTANCE (free from Core): continuousSMul_closedBall_closedBall

end ClosedBall

section Sphere

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): mulActionSphereBall

-- INSTANCE (free from Core): continuousSMul_sphere_ball

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): mulActionSphereClosedBall

-- INSTANCE (free from Core): continuousSMul_sphere_closedBall

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): mulActionSphereSphere

-- INSTANCE (free from Core): continuousSMul_sphere_sphere

end Sphere

section IsScalarTower

variable [NormedAlgebra 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' E]

-- INSTANCE (free from Core): isScalarTower_closedBall_closedBall_closedBall

-- INSTANCE (free from Core): isScalarTower_closedBall_closedBall_ball

-- INSTANCE (free from Core): isScalarTower_sphere_closedBall_closedBall

-- INSTANCE (free from Core): isScalarTower_sphere_closedBall_ball

-- INSTANCE (free from Core): isScalarTower_sphere_sphere_closedBall

-- INSTANCE (free from Core): isScalarTower_sphere_sphere_ball

-- INSTANCE (free from Core): isScalarTower_sphere_sphere_sphere

-- INSTANCE (free from Core): isScalarTower_sphere_ball_ball

-- INSTANCE (free from Core): isScalarTower_closedBall_ball_ball

end IsScalarTower

section SMulCommClass

variable [SMulCommClass 𝕜 𝕜' E]

-- INSTANCE (free from Core): instSMulCommClass_closedBall_closedBall_closedBall

-- INSTANCE (free from Core): instSMulCommClass_closedBall_closedBall_ball

-- INSTANCE (free from Core): instSMulCommClass_sphere_closedBall_closedBall

-- INSTANCE (free from Core): instSMulCommClass_sphere_closedBall_ball

-- INSTANCE (free from Core): instSMulCommClass_sphere_ball_ball

-- INSTANCE (free from Core): instSMulCommClass_sphere_sphere_closedBall

-- INSTANCE (free from Core): instSMulCommClass_sphere_sphere_ball

-- INSTANCE (free from Core): instSMulCommClass_sphere_sphere_sphere

end SMulCommClass

variable (𝕜)

variable [CharZero 𝕜]

include 𝕜 in

-- DISSOLVED: ne_neg_of_mem_sphere

include 𝕜 in

theorem ne_neg_of_mem_unit_sphere (x : sphere (0 : E) 1) : x ≠ -x :=
  ne_neg_of_mem_sphere 𝕜 one_ne_zero x
