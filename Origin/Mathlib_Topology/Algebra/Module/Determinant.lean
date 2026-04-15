/-
Extracted from Topology/Algebra/Module/Determinant.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The determinant of a continuous linear map.
-/

namespace ContinuousLinearMap

noncomputable abbrev det {R : Type*} [CommRing R] {M : Type*} [TopologicalSpace M] [AddCommGroup M]
    [Module R M] (A : M →L[R] M) : R :=
  LinearMap.det (A : M →ₗ[R] M)

theorem det_pi {ι R M : Type*} [Fintype ι] [CommRing R] [AddCommGroup M]
    [TopologicalSpace M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (f : ι → M →L[R] M) :
    (pi (fun i ↦ (f i).comp (proj i))).det = ∏ i, (f i).det :=
  LinearMap.det_pi _

theorem det_toSpanSingleton {𝕜 : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜] [ContinuousMul 𝕜]
    (v : 𝕜) : (toSpanSingleton 𝕜 v).det = v := by rw [← smulRight_id, det_smulRight]; simp
