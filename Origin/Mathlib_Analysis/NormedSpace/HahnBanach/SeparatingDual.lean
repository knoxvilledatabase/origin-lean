/-
Extracted from Analysis/NormedSpace/HahnBanach/SeparatingDual.lean
Genuine: 7 of 16 | Dissolved: 7 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.LinearAlgebra.Dual
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Spaces with separating dual

We introduce a typeclass `SeparatingDual R V`, registering that the points of the topological
module `V` over `R` can be separated by continuous linear forms.

This property is satisfied for normed spaces over `ℝ` or `ℂ` (by the analytic Hahn-Banach theorem)
and for locally convex topological spaces over `ℝ` (by the geometric Hahn-Banach theorem).

Under the assumption `SeparatingDual R V`, we show in
`SeparatingDual.exists_continuousLinearMap_apply_eq` that the group of continuous linear
equivalences acts transitively on the set of nonzero vectors.
-/

-- DISSOLVED: SeparatingDual

instance {E : Type*} [TopologicalSpace E] [AddCommGroup E] [TopologicalAddGroup E]
    [Module ℝ E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T1Space E] : SeparatingDual ℝ E :=
  ⟨fun x hx ↦ by
    rcases geometric_hahn_banach_point_point hx.symm with ⟨f, hf⟩
    simp only [map_zero] at hf
    exact ⟨f, hf.ne'⟩⟩

instance {E 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] : SeparatingDual 𝕜 E :=
  ⟨fun x hx ↦ by
    rcases exists_dual_vector 𝕜 x hx with ⟨f, -, hf⟩
    refine ⟨f, ?_⟩
    simpa [hf] using hx⟩

namespace SeparatingDual

section Ring

variable {R V : Type*} [Ring R] [AddCommGroup V] [TopologicalSpace V]
  [TopologicalSpace R] [Module R V] [SeparatingDual R V]

-- DISSOLVED: exists_ne_zero

theorem exists_separating_of_ne {x y : V} (h : x ≠ y) :
    ∃ f : V →L[R] R, f x ≠ f y := by
  rcases exists_ne_zero (R := R) (sub_ne_zero_of_ne h) with ⟨f, hf⟩
  exact ⟨f, by simpa [sub_ne_zero] using hf⟩

protected theorem t1Space [T1Space R] : T1Space V := by
  apply t1Space_iff_exists_open.2 (fun x y hxy ↦ ?_)
  rcases exists_separating_of_ne (R := R) hxy with ⟨f, hf⟩
  exact ⟨f ⁻¹' {f y}ᶜ, isOpen_compl_singleton.preimage f.continuous, hf, by simp⟩

protected theorem t2Space [T2Space R] : T2Space V := by
  apply (t2Space_iff _).2 (fun {x} {y} hxy ↦ ?_)
  rcases exists_separating_of_ne (R := R) hxy with ⟨f, hf⟩
  exact separated_by_continuous f.continuous hf

end Ring

section Field

variable {R V : Type*} [Field R] [AddCommGroup V] [TopologicalSpace R] [TopologicalSpace V]
  [TopologicalRing R] [Module R V]

theorem _root_.separatingDual_iff_injective : SeparatingDual R V ↔
    Function.Injective (ContinuousLinearMap.coeLM (R := R) R (M := V) (N₃ := R)).flip := by
  simp_rw [separatingDual_def, Ne, injective_iff_map_eq_zero]
  congrm ∀ v, ?_
  rw [not_imp_comm, LinearMap.ext_iff]
  push_neg; rfl

variable [SeparatingDual R V]

open Function in

theorem dualMap_surjective_iff {W} [AddCommGroup W] [Module R W] [FiniteDimensional R W]
    {f : W →ₗ[R] V} : Surjective (f.dualMap ∘ ContinuousLinearMap.toLinearMap) ↔ Injective f := by
  constructor <;> intro hf
  · exact LinearMap.dualMap_surjective_iff.mp hf.of_comp
  have := (separatingDual_iff_injective.mp ‹_›).comp hf
  rw [← LinearMap.coe_comp] at this
  exact LinearMap.flip_surjective_iff₁.mpr this

-- DISSOLVED: exists_eq_one

-- DISSOLVED: exists_eq_one_ne_zero_of_ne_zero_pair

variable [TopologicalAddGroup V]

-- DISSOLVED: exists_continuousLinearEquiv_apply_eq

open Filter

open scoped Topology

section

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [SeparatingDual 𝕜 E] [Nontrivial E]

lemma completeSpace_of_completeSpace_continuousLinearMap [CompleteSpace (E →L[𝕜] F)] :
    CompleteSpace F := by
  refine Metric.complete_of_cauchySeq_tendsto fun f hf => ?_
  obtain ⟨v, hv⟩ : ∃ (v : E), v ≠ 0 := exists_ne 0
  obtain ⟨φ, hφ⟩ : ∃ φ : E →L[𝕜] 𝕜, φ v = 1 := exists_eq_one hv
  let g : ℕ → (E →L[𝕜] F) := fun n ↦ ContinuousLinearMap.smulRightL 𝕜 E F φ (f n)
  have : CauchySeq g := (ContinuousLinearMap.smulRightL 𝕜 E F φ).lipschitz.cauchySeq_comp hf
  obtain ⟨a, ha⟩ : ∃ a, Tendsto g atTop (𝓝 a) := cauchy_iff_exists_le_nhds.mp this
  refine ⟨a v, ?_⟩
  have : Tendsto (fun n ↦ g n v) atTop (𝓝 (a v)) := by
    have : Continuous (fun (i : E →L[𝕜] F) ↦ i v) := by fun_prop
    exact (this.tendsto _).comp ha
  simpa [g, ContinuousLinearMap.smulRightL, hφ]

lemma completeSpace_continuousLinearMap_iff :
    CompleteSpace (E →L[𝕜] F) ↔ CompleteSpace F :=
  ⟨fun _h ↦ completeSpace_of_completeSpace_continuousLinearMap 𝕜 E F, fun _h ↦ inferInstance⟩

open ContinuousMultilinearMap

variable {ι : Type*} [Finite ι] {M : ι → Type*} [∀ i, NormedAddCommGroup (M i)]
  [∀ i, NormedSpace 𝕜 (M i)] [∀ i, SeparatingDual 𝕜 (M i)]

-- DISSOLVED: completeSpace_of_completeSpace_continuousMultilinearMap

-- DISSOLVED: completeSpace_continuousMultilinearMap_iff

end

end Field

end SeparatingDual
