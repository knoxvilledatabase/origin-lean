/-
Extracted from Geometry/Manifold/MFDeriv/SpecificFunctions.lean
Genuine: 22 of 22 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Differentiability of specific functions

In this file, we establish differentiability results for
- continuous linear maps and continuous linear equivalences
- the identity
- constant functions
- products
- arithmetic operations (such as addition and scalar multiplication).

-/

noncomputable section

open scoped Manifold

open Bundle Set Topology

section SpecificFunctions

/-! ### Differentiability of specific functions -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a charted space `M` over the pair `(E, H)`.
  {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M]
  -- declare a charted space `M'` over the pair `(E', H')`.
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  -- declare a charted space `M''` over the pair `(E'', H'')`.
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*}
  [TopologicalSpace M''] [ChartedSpace H'' M'']
  -- declare a charted space `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  -- declare a charted space `N'` over the pair `(F', G')`.
  {F' : Type*}
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type*} [TopologicalSpace G']
  {J' : ModelWithCorners 𝕜 F' G'} {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  -- F₁, F₂, F₃, F₄ are normed spaces
  {F₁ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {F₂ : Type*} [NormedAddCommGroup F₂]
  [NormedSpace 𝕜 F₂] {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] {F₄ : Type*}
  [NormedAddCommGroup F₄] [NormedSpace 𝕜 F₄]

namespace ContinuousLinearMap

variable (f : E →L[𝕜] E') {s : Set E} {x : E}

protected theorem hasMFDerivWithinAt : HasMFDerivAt[s] f x f :=
  f.hasFDerivWithinAt.hasMFDerivWithinAt

protected theorem hasMFDerivAt : HasMFDerivAt% f x f :=
  f.hasFDerivAt.hasMFDerivAt

protected theorem mdifferentiableWithinAt : MDiffAt[s] f x :=
  f.differentiableWithinAt.mdifferentiableWithinAt

protected theorem mdifferentiableOn : MDiff[s] f :=
  f.differentiableOn.mdifferentiableOn

protected theorem mdifferentiableAt : MDiffAt f x :=
  f.differentiableAt.mdifferentiableAt

protected theorem mdifferentiable : MDiff f :=
  f.differentiable.mdifferentiable

theorem mfderiv_eq : mfderiv% f x = f :=
  f.hasMFDerivAt.mfderiv

theorem mfderivWithin_eq (hs : UniqueMDiffWithinAt 𝓘(𝕜, E) s x) : mfderiv[s] f x = f :=
  f.hasMFDerivWithinAt.mfderivWithin hs

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable (f : E ≃L[𝕜] E') {s : Set E} {x : E}

protected theorem hasMFDerivWithinAt : HasMFDerivAt[s] f x (f : E →L[𝕜] E') :=
  f.hasFDerivWithinAt.hasMFDerivWithinAt

protected theorem hasMFDerivAt : HasMFDerivAt% f x (f : E →L[𝕜] E') :=
  f.hasFDerivAt.hasMFDerivAt

protected theorem mdifferentiableWithinAt : MDiffAt[s] f x :=
  f.differentiableWithinAt.mdifferentiableWithinAt

protected theorem mdifferentiableOn : MDiff[s] f :=
  f.differentiableOn.mdifferentiableOn

protected theorem mdifferentiableAt : MDiffAt f x :=
  f.differentiableAt.mdifferentiableAt

protected theorem mdifferentiable : MDiff f :=
  f.differentiable.mdifferentiable

theorem mfderiv_eq : mfderiv% f x = (f : E →L[𝕜] E') :=
  f.hasMFDerivAt.mfderiv

theorem mfderivWithin_eq (hs : UniqueMDiffWithinAt 𝓘(𝕜, E) s x) :
    mfderiv[s] f x = (f : E →L[𝕜] E') :=
  f.hasMFDerivWithinAt.mfderivWithin hs

end ContinuousLinearEquiv

variable {s : Set M} {x : M}

section id

/-! #### Identity -/

theorem hasMFDerivAt_id (x : M) :
    HasMFDerivAt I I (@id M) x (ContinuousLinearMap.id 𝕜 (TangentSpace I x)) := by
  refine ⟨continuousAt_id, ?_⟩
  have : ∀ᶠ y in 𝓝[range I] (extChartAt I x) x, (extChartAt I x ∘ (extChartAt I x).symm) y = y := by
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin x)
    mfld_set_tac
  apply HasFDerivWithinAt.congr_of_eventuallyEq (hasFDerivWithinAt_id _ _) this
  simp only [mfld_simps]

theorem hasMFDerivWithinAt_id (s : Set M) (x : M) :
    HasMFDerivAt[s] (@id M) x (ContinuousLinearMap.id 𝕜 (TangentSpace I x)) :=
  (hasMFDerivAt_id x).hasMFDerivWithinAt

theorem mdifferentiableAt_id : MDiffAt (@id M) x :=
  (hasMFDerivAt_id x).mdifferentiableAt

theorem mdifferentiableWithinAt_id : MDiffAt[s] (@id M) x :=
  mdifferentiableAt_id.mdifferentiableWithinAt

theorem mdifferentiable_id : MDiff (@id M) := fun _ ↦ mdifferentiableAt_id

theorem mdifferentiableOn_id : MDiff[s] (@id M) :=
  mdifferentiable_id.mdifferentiableOn
