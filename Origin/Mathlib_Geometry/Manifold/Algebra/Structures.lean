/-
Extracted from Geometry/Manifold/Algebra/Structures.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# `C^n` structures

In this file we define `C^n` structures that build on Lie groups. We prefer using the
term `ContMDiffRing` instead of Lie mainly because Lie ring has currently another use
in mathematics.
-/

open scoped Manifold ContDiff

section ContMDiffRing

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : WithTop ℕ∞}

class ContMDiffRing (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
    (R : Type*) [Semiring R] [TopologicalSpace R] [ChartedSpace H R] : Prop
    extends ContMDiffAdd I n R where
  contMDiff_mul : CMDiff n fun p : R × R => p.1 * p.2

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

end ContMDiffRing

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): (priority

variable {𝕜 R E H : Type*} [TopologicalSpace R] [TopologicalSpace H] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ChartedSpace H R] (I : ModelWithCorners 𝕜 E H)
  (n : WithTop ℕ∞)

theorem topologicalSemiring_of_contMDiffRing [Semiring R] [ContMDiffRing I n R] :
    IsTopologicalSemiring R :=
  { continuousMul_of_contMDiffMul I n, continuousAdd_of_contMDiffAdd I n with }
