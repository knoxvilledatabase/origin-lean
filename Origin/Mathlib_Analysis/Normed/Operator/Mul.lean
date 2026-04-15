/-
Extracted from Analysis/Normed/Operator/Mul.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Results about operator norms in normed algebras

This file (split off from `OperatorNorm.lean`) contains results about the operator norm
of multiplication and scalar-multiplication operations in normed algebras and normed modules.
-/

suppress_compilation

open Metric

open scoped NNReal Topology Uniformity

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]

section SemiNormed

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace ContinuousLinearMap

section MultiplicationLinear

section NonUnital

variable (𝕜) (R : Type*) [NonUnitalSeminormedRing R]

variable [NormedSpace 𝕜 R] [IsScalarTower 𝕜 R R] [SMulCommClass 𝕜 R R]

def mul : R →L[𝕜] R →L[𝕜] R :=
  (LinearMap.mul 𝕜 R).mkContinuous₂ 1 fun x y => by simpa using norm_mul_le x y
