/-
Extracted from MeasureTheory/Measure/Haar/Disintegration.lean
Genuine: 5 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Pushing a Haar measure by a linear map

We show that the push-forward of an additive Haar measure in a vector space under a surjective
linear map is proportional to the Haar measure on the target space,
in `LinearMap.exists_map_addHaar_eq_smul_addHaar`.

We deduce disintegration properties of the Haar measure: to check that a property is true ae,
it suffices to check that it is true ae along all translates of a given vector subspace.
See `MeasureTheory.ae_mem_of_ae_add_linearMap_mem`.

TODO: this holds more generally in any locally compact group, see
[Fremlin, *Measure Theory* (volume 4, 443Q)][fremlin_vol4]
-/

open MeasureTheory Measure Set

open scoped ENNReal

variable {𝕜 E F : Type*}
  [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F] [NormedSpace 𝕜 F] {L : E →ₗ[𝕜] F}
  {μ : Measure E} {ν : Measure F}
  [IsAddHaarMeasure μ] [IsAddHaarMeasure ν]

variable [LocallyCompactSpace E]

variable (L μ ν)

instance (T : Submodule 𝕜 E) : BorelSpace T := Subtype.borelSpace _

instance (T : Submodule 𝕜 E) : OpensMeasurableSpace T := Subtype.opensMeasurableSpace _

theorem LinearMap.exists_map_addHaar_eq_smul_addHaar' (h : Function.Surjective L) :
    ∃ (c : ℝ≥0∞), 0 < c ∧ c < ∞ ∧ μ.map L = (c * addHaar (univ : Set (LinearMap.ker L))) • ν := by
  /- This is true for the second projection in product spaces, as the projection of the Haar
  measure `μS.prod μT` is equal to the Haar measure `μT` multiplied by the total mass of `μS`. This
  is also true for linear equivalences, as they map Haar measure to Haar measure. The general case
  follows from these two and linear algebra, as `L` can be interpreted as the composition of the
  projection `P` on a complement `T` to its kernel `S`, together with a linear equivalence. -/
  have : FiniteDimensional 𝕜 E := .of_locallyCompactSpace 𝕜
  have : ProperSpace F := by
    rcases subsingleton_or_nontrivial E with hE|hE
    · have : Subsingleton F := Function.Surjective.subsingleton h
      infer_instance
    · have : ProperSpace 𝕜 := .of_locallyCompact_module 𝕜 E
      have : FiniteDimensional 𝕜 F := Module.Finite.of_surjective L h
      exact FiniteDimensional.proper 𝕜 F
  let S : Submodule 𝕜 E := LinearMap.ker L
  obtain ⟨T, hT⟩ : ∃ T : Submodule 𝕜 E, IsCompl S T := Submodule.exists_isCompl S
  let M : (S × T) ≃ₗ[𝕜] E := Submodule.prodEquivOfIsCompl S T hT
  have M_cont : Continuous M.symm := LinearMap.continuous_of_finiteDimensional _
  let P : S × T →ₗ[𝕜] T := LinearMap.snd 𝕜 S T
  have P_cont : Continuous P := LinearMap.continuous_of_finiteDimensional _
  have I : Function.Bijective (LinearMap.domRestrict L T) :=
    ⟨LinearMap.injective_domRestrict_iff.2 (IsCompl.inf_eq_bot hT.symm),
    (LinearMap.surjective_domRestrict_iff h).2 hT.symm.sup_eq_top⟩
  let L' : T ≃ₗ[𝕜] F := LinearEquiv.ofBijective (LinearMap.domRestrict L T) I
  have L'_cont : Continuous L' := LinearMap.continuous_of_finiteDimensional _
  have A : L = (L' : T →ₗ[𝕜] F).comp (P.comp (M.symm : E →ₗ[𝕜] (S × T))) := by
    ext x
    obtain ⟨y, z, hyz⟩ : ∃ (y : S) (z : T), M.symm x = (y, z) := ⟨_, _, rfl⟩
    have : x = M (y, z) := by
      rw [← hyz]; simp only [LinearEquiv.apply_symm_apply]
    simp [L', P, M, this]
  have I : μ.map L = ((μ.map M.symm).map P).map L' := by
    rw [Measure.map_map, Measure.map_map, A]
    · rfl
    · exact L'_cont.measurable.comp P_cont.measurable
    · exact M_cont.measurable
    · exact L'_cont.measurable
    · exact P_cont.measurable
  let μS : Measure S := addHaar
  let μT : Measure T := addHaar
  obtain ⟨c₀, c₀_pos, c₀_fin, h₀⟩ :
      ∃ c₀ : ℝ≥0∞, c₀ ≠ 0 ∧ c₀ ≠ ∞ ∧ μ.map M.symm = c₀ • μS.prod μT := by
    have : IsAddHaarMeasure (μ.map M.symm) :=
      M.toContinuousLinearEquiv.symm.isAddHaarMeasure_map μ
    refine ⟨addHaarScalarFactor (μ.map M.symm) (μS.prod μT), ?_, ENNReal.coe_ne_top,
      isAddLeftInvariant_eq_smul _ _⟩
    simpa only [ne_eq, ENNReal.coe_eq_zero] using
      (addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map M.symm) (μS.prod μT)).ne'
  have J : (μS.prod μT).map P = (μS univ) • μT := map_snd_prod
  obtain ⟨c₁, c₁_pos, c₁_fin, h₁⟩ : ∃ c₁ : ℝ≥0∞, c₁ ≠ 0 ∧ c₁ ≠ ∞ ∧ μT.map L' = c₁ • ν := by
    have : IsAddHaarMeasure (μT.map L') :=
      L'.toContinuousLinearEquiv.isAddHaarMeasure_map μT
    refine ⟨addHaarScalarFactor (μT.map L') ν, ?_, ENNReal.coe_ne_top,
      isAddLeftInvariant_eq_smul _ _⟩
    simpa only [ne_eq, ENNReal.coe_eq_zero] using
      (addHaarScalarFactor_pos_of_isAddHaarMeasure (μT.map L') ν).ne'
  refine ⟨c₀ * c₁, by simp [pos_iff_ne_zero, c₀_pos, c₁_pos],
    ENNReal.mul_lt_top c₀_fin.lt_top c₁_fin.lt_top, ?_⟩
  simp only [I, h₀, Measure.map_smul, J, smul_smul, h₁]
  rw [mul_assoc, mul_comm _ c₁, ← mul_assoc]

theorem LinearMap.exists_map_addHaar_eq_smul_addHaar (h : Function.Surjective L) :
    ∃ (c : ℝ≥0∞), 0 < c ∧ μ.map L = c • ν := by
  rcases L.exists_map_addHaar_eq_smul_addHaar' μ ν h with ⟨c, c_pos, -, hc⟩
  exact ⟨_, by simp [c_pos, NeZero.ne addHaar], hc⟩

namespace MeasureTheory

lemma ae_comp_linearMap_mem_iff (h : Function.Surjective L) {s : Set F} (hs : MeasurableSet s) :
    (∀ᵐ x ∂μ, L x ∈ s) ↔ ∀ᵐ y ∂ν, y ∈ s := by
  have : FiniteDimensional 𝕜 E := .of_locallyCompactSpace 𝕜
  have : AEMeasurable L μ := L.continuous_of_finiteDimensional.aemeasurable
  apply (ae_map_iff this hs).symm.trans
  rcases L.exists_map_addHaar_eq_smul_addHaar μ ν h with ⟨c, c_pos, hc⟩
  rw [hc]
  exact ae_smul_measure_iff c_pos.ne'

lemma ae_ae_add_linearMap_mem_iff [LocallyCompactSpace F] {s : Set F} (hs : MeasurableSet s) :
    (∀ᵐ y ∂ν, ∀ᵐ x ∂μ, y + L x ∈ s) ↔ ∀ᵐ y ∂ν, y ∈ s := by
  have : FiniteDimensional 𝕜 E := .of_locallyCompactSpace 𝕜
  have : FiniteDimensional 𝕜 F := .of_locallyCompactSpace 𝕜
  have : ProperSpace E := .of_locallyCompactSpace 𝕜
  have : ProperSpace F := .of_locallyCompactSpace 𝕜
  let M : F × E →ₗ[𝕜] F := LinearMap.id.coprod L
  have M_cont : Continuous M := M.continuous_of_finiteDimensional
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `range_eq_top` into
  -- `range_eq_top (f := _)`
  have hM : Function.Surjective M := by
    simp [M, ← LinearMap.range_eq_top (f := _), LinearMap.range_coprod]
  have A : ∀ x, M x ∈ s ↔ x ∈ M ⁻¹' s := fun x ↦ Iff.rfl
  simp_rw [← ae_comp_linearMap_mem_iff M (ν.prod μ) ν hM hs, A]
  rw [Measure.ae_prod_mem_iff_ae_ae_mem]
  · simp only [M, mem_preimage, LinearMap.coprod_apply, LinearMap.id_coe, id_eq]
  · exact M_cont.measurable hs

lemma ae_mem_of_ae_add_linearMap_mem [LocallyCompactSpace F] {s : Set F} (hs : MeasurableSet s)
    (h : ∀ y, ∀ᵐ x ∂μ, y + L x ∈ s) : ∀ᵐ y ∂ν, y ∈ s :=
  (ae_ae_add_linearMap_mem_iff L μ ν hs).1 (Filter.Eventually.of_forall h)

end MeasureTheory
