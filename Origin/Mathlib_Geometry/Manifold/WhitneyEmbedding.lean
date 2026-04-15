/-
Extracted from Geometry/Manifold/WhitneyEmbedding.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Whitney embedding theorem

In this file we prove a version of the Whitney embedding theorem: for any compact real manifold `M`,
for sufficiently large `n` there exists a smooth embedding `M → ℝ^n`.

## TODO

* Prove the weak Whitney embedding theorem: any `σ`-compact smooth `m`-dimensional manifold can be
  embedded into `ℝ^(2m+1)`. This requires a version of Sard's theorem: for a locally Lipschitz
  continuous map `f : ℝ^m → ℝ^n`, `m < n`, the range has Hausdorff dimension at most `m`, hence it
  has measure zero.

## Tags

partition of unity, smooth bump function, whitney theorem
-/

universe uι uE uH uM

open Function Filter Module Set Topology

open scoped Manifold ContDiff

variable {ι : Type uι} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable section

namespace SmoothBumpCovering

/-!
### Whitney embedding theorem

In this section we prove a version of the Whitney embedding theorem: for any compact real manifold
`M`, for sufficiently large `n` there exists a smooth embedding `M → ℝ^n`.
-/

variable [T2Space M] [Fintype ι] {s : Set M} (f : SmoothBumpCovering ι I M s)

def embeddingPiTangent : C^∞⟮I, M; 𝓘(ℝ, ι → E × ℝ), ι → E × ℝ⟯ where
  val x i := (f i x • extChartAt I (f.c i) x, f i x)
  property :=
    contMDiff_pi_space.2 fun i =>
      ((f i).contMDiff_smul contMDiffOn_extChartAt).prodMk_space (f i).contMDiff
