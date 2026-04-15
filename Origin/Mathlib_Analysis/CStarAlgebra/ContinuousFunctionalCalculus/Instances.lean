/-
Extracted from Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Instances.lean
Genuine: 14 of 16 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-! # Instances of the continuous functional calculus

## Main theorems

* `IsSelfAdjoint.instContinuousFunctionalCalculus`: the continuous functional calculus for
  selfadjoint elements in a `ℂ`-algebra with a continuous functional calculus for normal elements
  and where every element has compact spectrum. In particular, this includes unital C⋆-algebras
  over `ℂ`.
* `Nonneg.instContinuousFunctionalCalculus`: the continuous functional calculus for nonnegative
  elements in an `ℝ`-algebra with a continuous functional calculus for selfadjoint elements,
  where every element has compact spectrum, and where nonnegative elements have nonnegative
  spectrum. In particular, this includes unital C⋆-algebras over `ℝ`.

## Tags

continuous functional calculus, normal, selfadjoint
-/

open Topology

noncomputable section

local notation "σₙ" => quasispectrum

local notation "σ" => spectrum

/-!
### Pull back a non-unital instance from a unital one on the unitization
-/

section RCLike

variable {𝕜 A : Type*} [RCLike 𝕜] [NonUnitalNormedRing A] [StarRing A]

variable [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

variable [StarModule 𝕜 A] {p : A → Prop} {p₁ : Unitization 𝕜 A → Prop}

local postfix:max "⁺¹" => Unitization 𝕜

variable (hp₁ : ∀ {x : A}, p₁ x ↔ p x) (a : A) (ha : p a)

variable [ClosedEmbeddingContinuousFunctionalCalculus 𝕜 (Unitization 𝕜 A) p₁]

open scoped ContinuousMapZero

open Unitization in

noncomputable def cfcₙAux : C(σₙ 𝕜 a, 𝕜)₀ →⋆ₙₐ[𝕜] A⁺¹ :=
  (cfcHom (R := 𝕜) (hp₁.mpr ha) : C(σ 𝕜 (a : A⁺¹), 𝕜) →⋆ₙₐ[𝕜] A⁺¹) |>.comp
    (Homeomorph.compStarAlgEquiv' 𝕜 𝕜 <| .setCongr <| (quasispectrum_eq_spectrum_inr' 𝕜 𝕜 a).symm)
    |>.comp ContinuousMapZero.toContinuousMapHom

lemma cfcₙAux_id : cfcₙAux hp₁ a ha (.id _) = a := cfcHom_id (hp₁.mpr ha)

lemma continuous_cfcₙAux : Continuous (cfcₙAux hp₁ a ha) :=
  (cfcHom_continuous (hp₁.mpr ha)).comp <|
    (ContinuousMap.continuous_precomp _).comp <|
    ContinuousMapZero.isEmbedding_toContinuousMap.continuous

lemma cfcₙAux_injective : Function.Injective (cfcₙAux hp₁ a ha) :=
  (cfcHom_injective (hp₁.mpr ha)).comp <|
    .comp (Equiv.injective _) ContinuousMapZero.isEmbedding_toContinuousMap.injective

lemma spec_cfcₙAux (f : C(σₙ 𝕜 a, 𝕜)₀) : σ 𝕜 (cfcₙAux hp₁ a ha f) = Set.range f := by
  rw [cfcₙAux, NonUnitalStarAlgHom.comp_assoc, NonUnitalStarAlgHom.comp_apply]
  simp only [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_coe]
  rw [cfcHom_map_spectrum (hp₁.mpr ha) (R := 𝕜) _]
  simp

open Unitization in

lemma isClosedEmbedding_cfcₙAux : IsClosedEmbedding (cfcₙAux hp₁ a ha) := by
  simp only [cfcₙAux, NonUnitalStarAlgHom.coe_comp]
  refine ((cfcHom_isClosedEmbedding (hp₁.mpr ha)).comp ?_).comp
    ContinuousMapZero.isClosedEmbedding_toContinuousMap
  let e : C(σₙ 𝕜 a, 𝕜) ≃ₜ C(σ 𝕜 (a : A⁺¹), 𝕜) :=
    (Homeomorph.setCongr (quasispectrum_eq_spectrum_inr' 𝕜 𝕜 a)).arrowCongr (.refl _)
  exact e.isClosedEmbedding

variable [CompleteSpace A]

lemma cfcₙAux_mem_range_inr (f : C(σₙ 𝕜 a, 𝕜)₀) :
    cfcₙAux hp₁ a ha f ∈ NonUnitalStarAlgHom.range (Unitization.inrNonUnitalStarAlgHom 𝕜 A) := by
  have h₁ := (continuous_cfcₙAux hp₁ a ha).range_subset_closure_image_dense
    (ContinuousMapZero.adjoin_id_dense (σₙ 𝕜 a)) ⟨f, rfl⟩
  rw [← SetLike.mem_coe]
  refine closure_minimal ?_ ?_ h₁
  · rw [← NonUnitalStarSubalgebra.coe_map, SetLike.coe_subset_coe, NonUnitalStarSubalgebra.map_le]
    apply NonUnitalStarAlgebra.adjoin_le
    apply Set.singleton_subset_iff.mpr
    rw [SetLike.mem_coe, NonUnitalStarSubalgebra.mem_comap, cfcₙAux_id hp₁ a ha]
    exact ⟨a, rfl⟩
  · simp only [NonUnitalStarAlgHom.coe_range]
    convert IsClosed.preimage (Unitization.continuous_fst (𝕜 := 𝕜)) isClosed_singleton
    aesop

variable [CStarRing A]

include hp₁ in

open Unitization NonUnitalStarAlgHom in

theorem RCLike.nonUnitalContinuousFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus 𝕜 A p where
  predicate_zero := by
    rw [← hp₁, Unitization.inr_zero 𝕜]
    exact cfc_predicate_zero 𝕜
  exists_cfc_of_predicate a ha := by
    let ψ : C(σₙ 𝕜 a, 𝕜)₀ →⋆ₙₐ[𝕜] A := comp (inrRangeEquiv 𝕜 A).symm <|
      codRestrict (cfcₙAux hp₁ a ha) _ (cfcₙAux_mem_range_inr hp₁ a ha)
    have coe_ψ (f : C(σₙ 𝕜 a, 𝕜)₀) : ψ f = cfcₙAux hp₁ a ha f :=
      congr_arg Subtype.val <| (inrRangeEquiv 𝕜 A).apply_symm_apply
        ⟨cfcₙAux hp₁ a ha f, cfcₙAux_mem_range_inr hp₁ a ha f⟩
    refine ⟨ψ, ?continuous, ?injective, ?map_id, fun f ↦ ?map_spec, fun f ↦ ?isStarNormal⟩
    case continuous =>
      rw [isometry_inr (𝕜 := 𝕜) |>.isEmbedding.continuous_iff]
      have := continuous_cfcₙAux hp₁ a ha
      simp only [coe_comp, NonUnitalStarAlgHom.coe_coe, Function.comp_def,
        inrRangeEquiv_symm_apply, coe_codRestrict, ψ]
      fun_prop
    case injective => simpa [ψ] using
      (inrRangeEquiv 𝕜 A).symm.injective.comp (cfcₙAux_injective hp₁ a ha).codRestrict
    case map_id => exact inr_injective (R := 𝕜) <| coe_ψ _ ▸ cfcₙAux_id hp₁ a ha
    case map_spec =>
      exact quasispectrum_eq_spectrum_inr' 𝕜 𝕜 (ψ f) ▸ coe_ψ _ ▸ spec_cfcₙAux hp₁ a ha f
    case isStarNormal => exact hp₁.mp <| coe_ψ _ ▸ cfcHom_predicate (R := 𝕜) (hp₁.mpr ha) _

open Unitization in

open scoped NonUnitalContinuousFunctionalCalculus in

lemma inrNonUnitalStarAlgHom_comp_cfcₙHom_eq_cfcₙAux (a : A) (ha : p a) :
    letI _ := RCLike.nonUnitalContinuousFunctionalCalculus hp₁
    (inrNonUnitalStarAlgHom 𝕜 A).comp (cfcₙHom ha) = cfcₙAux hp₁ a ha := by
  letI _ := RCLike.nonUnitalContinuousFunctionalCalculus hp₁
  apply ContinuousMapZero.UniqueHom.eq_of_continuous_of_map_id _ _ _
    (Unitization.continuous_inr.comp <| cfcₙHom_continuous ha)
    (continuous_cfcₙAux hp₁ a ha)
    (by simp [cfcₙHom_id ha, cfcₙAux_id hp₁ a ha])
  all_goals infer_instance

include hp₁ in

open Unitization NonUnitalStarAlgHom in

theorem RCLike.nonUnitalContinuousFunctionalCalculusIsClosedEmbedding :
    NonUnitalClosedEmbeddingContinuousFunctionalCalculus 𝕜 A p where
  toNonUnitalContinuousFunctionalCalculus := RCLike.nonUnitalContinuousFunctionalCalculus hp₁
  isClosedEmbedding a ha := by
    apply isometry_inr (𝕜 := 𝕜) (A := A) |>.isClosedEmbedding |>.of_comp_iff.mp
    convert isClosedEmbedding_cfcₙAux hp₁ a ha
    congrm (⇑$(inrNonUnitalStarAlgHom_comp_cfcₙHom_eq_cfcₙAux hp₁ a ha))

end RCLike

/-!
### Continuous functional calculus for selfadjoint elements
-/

section SelfAdjointNonUnital

variable {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal]

set_option backward.isDefEq.respectTransparency false in

lemma isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts {a : A} :
    IsSelfAdjoint a ↔ IsStarNormal a ∧ QuasispectrumRestricts a Complex.reCLM := by
  refine ⟨fun ha ↦ ⟨ha.isStarNormal, ⟨fun x hx ↦ ?_, Complex.ofReal_re⟩⟩, ?_⟩
  · have := eqOn_of_cfcₙ_eq_cfcₙ <|
      (cfcₙ_star (id : ℂ → ℂ) a).symm ▸ (cfcₙ_id ℂ a).symm ▸ ha.star_eq
    exact Complex.conj_eq_iff_re.mp (by simpa using this hx)
  · rintro ⟨ha₁, ha₂⟩
    rw [isSelfAdjoint_iff]
    nth_rw 2 [← cfcₙ_id ℂ a]
    rw [← cfcₙ_star_id a (R := ℂ)]
    refine cfcₙ_congr fun x hx ↦ ?_
    obtain ⟨x, -, rfl⟩ := ha₂.algebraMap_image.symm ▸ hx
    exact Complex.conj_ofReal _

lemma IsSelfAdjoint.quasispectrumRestricts {a : A} (ha : IsSelfAdjoint a) :
    QuasispectrumRestricts a Complex.reCLM :=
  isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts |>.mp ha |>.2

lemma QuasispectrumRestricts.isSelfAdjoint (a : A) (ha : QuasispectrumRestricts a Complex.reCLM)
    [IsStarNormal a] : IsSelfAdjoint a :=
  isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts.mpr ⟨‹_›, ha⟩

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

end SelfAdjointNonUnital

section SelfAdjointUnital

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra ℂ A]
  [ContinuousFunctionalCalculus ℂ A IsStarNormal]

lemma IsSelfAdjoint.spectrumRestricts {a : A} (ha : IsSelfAdjoint a) :
    SpectrumRestricts a Complex.reCLM :=
  ha.quasispectrumRestricts

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): IsSelfAdjoint.instContinuousFunctionalCalculus
