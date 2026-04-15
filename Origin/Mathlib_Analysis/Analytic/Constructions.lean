/-
Extracted from Analysis/Analytic/Constructions.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Various ways to combine analytic functions

We show that the following are analytic:

1. Cartesian products of analytic functions
2. Arithmetic on analytic functions: `mul`, `smul`, `inv`, `div`
3. Finite sums and products: `Finset.sum`, `Finset.prod`
-/

noncomputable section

open scoped Topology Ring

open Filter Asymptotics ENNReal NNReal

variable {α : Type*}

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H]
  [NormedSpace 𝕜 H]

variable {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]

variable {𝕝 : Type*} [NormedDivisionRing 𝕝] [NormedAlgebra 𝕜 𝕝]

/-!
### Constants are analytic
-/

theorem hasFPowerSeriesOnBall_const {c : F} {e : E} :
    HasFPowerSeriesOnBall (fun _ => c) (constFormalMultilinearSeries 𝕜 E c) e ⊤ := by
  refine ⟨by simp, WithTop.top_pos, fun _ => hasSum_single 0 fun n hn => ?_⟩
  simp [constFormalMultilinearSeries_apply_of_nonzero hn]

theorem hasFPowerSeriesAt_const {c : F} {e : E} :
    HasFPowerSeriesAt (fun _ => c) (constFormalMultilinearSeries 𝕜 E c) e :=
  ⟨⊤, hasFPowerSeriesOnBall_const⟩
