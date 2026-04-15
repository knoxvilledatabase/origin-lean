/-
Extracted from Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Isometric.lean
Genuine: 40 | Conflates: 4 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-! # Isometric continuous functional calculus

This file adds a class for an *isometric* continuous functional calculus. This is separate from the
usual `ContinuousFunctionalCalculus` class because we prefer not to require a metric (or a norm) on
the algebra for reasons discussed in the module documentation for that file.

Of course, with a metric on the algebra and an isometric continuous functional calculus, the
algebra must *be* a C⋆-algebra already. As such, it may seem like this class is not useful. However,
the main purpose is to allow for the continuous functional calculus to be a isometric for the other
scalar rings `ℝ` and `ℝ≥0` too.
-/

local notation "σ" => spectrum

local notation "σₙ" => quasispectrum

/-! ### Isometric continuous functional calculus for unital algebras -/

section Unital

class IsometricContinuousFunctionalCalculus (R A : Type*) (p : outParam (A → Prop))
    [CommSemiring R] [StarRing R] [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R]
    [Ring A] [StarRing A] [MetricSpace A] [Algebra R A]
    extends ContinuousFunctionalCalculus R p : Prop where
  isometric (a : A) (ha : p a) : Isometry (cfcHom ha (R := R))

section MetricSpace

open scoped ContinuousFunctionalCalculus

lemma isometry_cfcHom {R A : Type*} {p : outParam (A → Prop)} [CommSemiring R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [MetricSpace A] [Algebra R A] [IsometricContinuousFunctionalCalculus R A p]
    (a : A) (ha : p a := by cfc_tac) :
    Isometry (cfcHom (show p a from ha) (R := R)) :=
  IsometricContinuousFunctionalCalculus.isometric a ha

end MetricSpace

section NormedRing

open scoped ContinuousFunctionalCalculus

variable {𝕜 A : Type*} {p : outParam (A → Prop)}

variable [RCLike 𝕜] [NormedRing A] [StarRing A] [NormedAlgebra 𝕜 A]

variable [IsometricContinuousFunctionalCalculus 𝕜 A p]

lemma norm_cfcHom (a : A) (f : C(σ 𝕜 a, 𝕜)) (ha : p a := by cfc_tac) :
    ‖cfcHom (show p a from ha) f‖ = ‖f‖ := by
  refine isometry_cfcHom a |>.norm_map_of_map_zero (map_zero _) f

lemma nnnorm_cfcHom (a : A) (f : C(σ 𝕜 a, 𝕜)) (ha : p a := by cfc_tac) :
    ‖cfcHom (show p a from ha) f‖₊ = ‖f‖₊ :=
  Subtype.ext <| norm_cfcHom a f ha

-- CONFLATES (assumes ground = zero): IsGreatest.norm_cfc
lemma IsGreatest.norm_cfc [Nontrivial A] (f : 𝕜 → 𝕜) (a : A)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    IsGreatest ((fun x ↦ ‖f x‖) '' spectrum 𝕜 a) ‖cfc f a‖ := by
  obtain ⟨x, hx⟩ := ContinuousFunctionalCalculus.isCompact_spectrum a
    |>.image_of_continuousOn hf.norm |>.exists_isGreatest <|
    (ContinuousFunctionalCalculus.spectrum_nonempty a ha).image _
  obtain ⟨x, hx', rfl⟩ := hx.1
  convert hx
  rw [cfc_apply f a, norm_cfcHom a _]
  apply le_antisymm
  · apply ContinuousMap.norm_le _ (norm_nonneg _) |>.mpr
    rintro ⟨y, hy⟩
    exact hx.2 ⟨y, hy, rfl⟩
  · exact le_trans (by simp) <| ContinuousMap.norm_coe_le_norm _ (⟨x, hx'⟩ : σ 𝕜 a)

-- CONFLATES (assumes ground = zero): IsGreatest.nnnorm_cfc
lemma IsGreatest.nnnorm_cfc [Nontrivial A] (f : 𝕜 → 𝕜) (a : A)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    IsGreatest ((fun x ↦ ‖f x‖₊) '' σ 𝕜 a) ‖cfc f a‖₊ := by
  convert Real.toNNReal_mono.map_isGreatest (.norm_cfc f a)
  all_goals simp [Set.image_image, norm_toNNReal]

lemma norm_apply_le_norm_cfc (f : 𝕜 → 𝕜) (a : A) ⦃x : 𝕜⦄ (hx : x ∈ σ 𝕜 a)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    ‖f x‖ ≤ ‖cfc f a‖ := by
  revert hx
  nontriviality A
  exact (IsGreatest.norm_cfc f a hf ha |>.2 ⟨x, ·, rfl⟩)

lemma nnnorm_apply_le_nnnorm_cfc (f : 𝕜 → 𝕜) (a : A) ⦃x : 𝕜⦄ (hx : x ∈ σ 𝕜 a)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    ‖f x‖₊ ≤ ‖cfc f a‖₊ :=
  norm_apply_le_norm_cfc f a hx

lemma norm_cfc_le {f : 𝕜 → 𝕜} {a : A} {c : ℝ} (hc : 0 ≤ c) (h : ∀ x ∈ σ 𝕜 a, ‖f x‖ ≤ c) :
    ‖cfc f a‖ ≤ c := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simpa [Subsingleton.elim (cfc f a) 0]
  · refine cfc_cases (‖·‖ ≤ c) a f (by simpa) fun hf ha ↦ ?_
    simp only [← cfc_apply f a, isLUB_le_iff (IsGreatest.norm_cfc f a hf ha |>.isLUB)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

lemma norm_cfc_le_iff (f : 𝕜 → 𝕜) (a : A) {c : ℝ} (hc : 0 ≤ c)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : ‖cfc f a‖ ≤ c ↔ ∀ x ∈ σ 𝕜 a, ‖f x‖ ≤ c :=
  ⟨fun h _ hx ↦ norm_apply_le_norm_cfc f a hx hf ha |>.trans h, norm_cfc_le hc⟩

lemma norm_cfc_lt {f : 𝕜 → 𝕜} {a : A} {c : ℝ} (hc : 0 < c) (h : ∀ x ∈ σ 𝕜 a, ‖f x‖ < c) :
    ‖cfc f a‖ < c := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simpa [Subsingleton.elim (cfc f a) 0]
  · refine cfc_cases (‖·‖ < c) a f (by simpa) fun hf ha ↦ ?_
    simp only [← cfc_apply f a, (IsGreatest.norm_cfc f a hf ha |>.lt_iff)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

lemma norm_cfc_lt_iff (f : 𝕜 → 𝕜) (a : A) {c : ℝ} (hc : 0 < c)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : ‖cfc f a‖ < c ↔ ∀ x ∈ σ 𝕜 a, ‖f x‖ < c :=
  ⟨fun h _ hx ↦ norm_apply_le_norm_cfc f a hx hf ha |>.trans_lt h, norm_cfc_lt hc⟩

open NNReal

lemma nnnorm_cfc_le {f : 𝕜 → 𝕜} {a : A} (c : ℝ≥0) (h : ∀ x ∈ σ 𝕜 a, ‖f x‖₊ ≤ c) :
    ‖cfc f a‖₊ ≤ c :=
  norm_cfc_le c.2 h

lemma nnnorm_cfc_le_iff (f : 𝕜 → 𝕜) (a : A) (c : ℝ≥0)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : ‖cfc f a‖₊ ≤ c ↔ ∀ x ∈ σ 𝕜 a, ‖f x‖₊ ≤ c :=
  norm_cfc_le_iff f a c.2

lemma nnnorm_cfc_lt {f : 𝕜 → 𝕜} {a : A} {c : ℝ≥0} (hc : 0 < c) (h : ∀ x ∈ σ 𝕜 a, ‖f x‖₊ < c) :
    ‖cfc f a‖₊ < c :=
  norm_cfc_lt hc h

lemma nnnorm_cfc_lt_iff (f : 𝕜 → 𝕜) (a : A) {c : ℝ≥0} (hc : 0 < c)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : ‖cfc f a‖₊ < c ↔ ∀ x ∈ σ 𝕜 a, ‖f x‖₊ < c :=
  norm_cfc_lt_iff f a hc

end NormedRing

namespace SpectrumRestricts

variable {R S A : Type*} {p q : A → Prop}

variable [Semifield R] [StarRing R] [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R]

variable [Semifield S] [StarRing S] [MetricSpace S] [TopologicalSemiring S] [ContinuousStar S]

variable [Ring A] [StarRing A] [Algebra S A]

variable [Algebra R S] [Algebra R A] [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S]

variable [MetricSpace A] [IsometricContinuousFunctionalCalculus S A q]

variable [CompleteSpace R] [UniqueContinuousFunctionalCalculus R A]

open scoped ContinuousFunctionalCalculus in

protected theorem isometric_cfc (f : C(S, R)) (halg : Isometry (algebraMap R S)) (h0 : p 0)
    (h : ∀ a, p a ↔ q a ∧ SpectrumRestricts a f) :
    IsometricContinuousFunctionalCalculus R A p where
  toContinuousFunctionalCalculus := SpectrumRestricts.cfc f halg.isUniformEmbedding h0 h
  isometric a ha := by
    obtain ⟨ha', haf⟩ := h a |>.mp ha
    have _inst (a : A) : CompactSpace (σ R a) := by
      rw [← isCompact_iff_compactSpace, ← spectrum.preimage_algebraMap S]
      exact halg.isClosedEmbedding.isCompact_preimage <|
        ContinuousFunctionalCalculus.isCompact_spectrum a
    have := SpectrumRestricts.cfc f halg.isUniformEmbedding h0 h
    rw [cfcHom_eq_restrict f halg.isUniformEmbedding ha ha' haf]
    refine .of_dist_eq fun g₁ g₂ ↦ ?_
    simp only [starAlgHom_apply, isometry_cfcHom a ha' |>.dist_eq]
    refine le_antisymm ?_ ?_
    all_goals refine ContinuousMap.dist_le dist_nonneg |>.mpr fun x ↦ ?_
    · simpa [halg.dist_eq] using ContinuousMap.dist_apply_le_dist _
    · let x' : σ S a := Subtype.map (algebraMap R S) (fun _ ↦ spectrum.algebraMap_mem S) x
      apply le_of_eq_of_le ?_ <| ContinuousMap.dist_apply_le_dist x'
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, StarAlgHom.ofId_apply,
        halg.dist_eq, x']
      congr!
      all_goals ext; exact haf.left_inv _ |>.symm

end SpectrumRestricts

end Unital

/-! ### Isometric continuous functional calculus for non-unital algebras -/

section NonUnital

-- CONFLATES (assumes ground = zero): NonUnitalIsometricContinuousFunctionalCalculus
class NonUnitalIsometricContinuousFunctionalCalculus (R A : Type*) (p : outParam (A → Prop))
    [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R] [TopologicalSemiring R]
    [ContinuousStar R] [NonUnitalRing A] [StarRing A] [MetricSpace A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    extends NonUnitalContinuousFunctionalCalculus R p : Prop where
  isometric (a : A) (ha : p a) : Isometry (cfcₙHom ha (R := R))

section MetricSpace

variable {R A : Type*} {p : outParam (A → Prop)}

variable [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R] [TopologicalSemiring R]

variable [ContinuousStar R]

variable [NonUnitalRing A] [StarRing A] [MetricSpace A] [Module R A]

variable [IsScalarTower R A A] [SMulCommClass R A A]

open scoped NonUnitalContinuousFunctionalCalculus

variable [NonUnitalIsometricContinuousFunctionalCalculus R A p]

lemma isometry_cfcₙHom (a : A) (ha : p a := by cfc_tac) :
    Isometry (cfcₙHom (show p a from ha) (R := R)) :=
  NonUnitalIsometricContinuousFunctionalCalculus.isometric a ha

end MetricSpace

section NormedRing

variable {𝕜 A : Type*} {p : outParam (A → Prop)}

variable [RCLike 𝕜] [NonUnitalNormedRing A] [StarRing A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A]

variable [SMulCommClass 𝕜 A A]

variable [NonUnitalIsometricContinuousFunctionalCalculus 𝕜 A p]

open NonUnitalIsometricContinuousFunctionalCalculus

open scoped ContinuousMapZero NonUnitalContinuousFunctionalCalculus

lemma norm_cfcₙHom (a : A) (f : C(σₙ 𝕜 a, 𝕜)₀) (ha : p a := by cfc_tac) :
    ‖cfcₙHom (show p a from ha) f‖ = ‖f‖ := by
  refine isometry_cfcₙHom a |>.norm_map_of_map_zero (map_zero _) f

lemma nnnorm_cfcₙHom (a : A) (f : C(σₙ 𝕜 a, 𝕜)₀) (ha : p a := by cfc_tac) :
    ‖cfcₙHom (show p a from ha) f‖₊ = ‖f‖₊ :=
  Subtype.ext <| norm_cfcₙHom a f ha

lemma IsGreatest.norm_cfcₙ (f : 𝕜 → 𝕜) (a : A)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : IsGreatest ((fun x ↦ ‖f x‖) '' σₙ 𝕜 a) ‖cfcₙ f a‖ := by
  obtain ⟨x, hx⟩ := NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum a
      |>.image_of_continuousOn hf.norm |>.exists_isGreatest <|
      (quasispectrum.nonempty 𝕜 a).image _
  obtain ⟨x, hx', rfl⟩ := hx.1
  convert hx
  rw [cfcₙ_apply f a, norm_cfcₙHom a _]
  apply le_antisymm
  · apply ContinuousMap.norm_le _ (norm_nonneg _) |>.mpr
    rintro ⟨y, hy⟩
    exact hx.2 ⟨y, hy, rfl⟩
  · exact le_trans (by simp) <| ContinuousMap.norm_coe_le_norm _ (⟨x, hx'⟩ : σₙ 𝕜 a)

lemma IsGreatest.nnnorm_cfcₙ (f : 𝕜 → 𝕜) (a : A)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : IsGreatest ((fun x ↦ ‖f x‖₊) '' σₙ 𝕜 a) ‖cfcₙ f a‖₊ := by
  convert Real.toNNReal_mono.map_isGreatest (.norm_cfcₙ f a)
  all_goals simp [Set.image_image, norm_toNNReal]

lemma norm_apply_le_norm_cfcₙ (f : 𝕜 → 𝕜) (a : A) ⦃x : 𝕜⦄ (hx : x ∈ σₙ 𝕜 a)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : ‖f x‖ ≤ ‖cfcₙ f a‖ :=
  IsGreatest.norm_cfcₙ f a hf hf₀ ha |>.2 ⟨x, hx, rfl⟩

lemma nnnorm_apply_le_nnnorm_cfcₙ (f : 𝕜 → 𝕜) (a : A) ⦃x : 𝕜⦄ (hx : x ∈ σₙ 𝕜 a)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : ‖f x‖₊ ≤ ‖cfcₙ f a‖₊ :=
  IsGreatest.nnnorm_cfcₙ f a hf hf₀ ha |>.2 ⟨x, hx, rfl⟩

lemma norm_cfcₙ_le {f : 𝕜 → 𝕜} {a : A} {c : ℝ} (h : ∀ x ∈ σₙ 𝕜 a, ‖f x‖ ≤ c) :
    ‖cfcₙ f a‖ ≤ c := by
  refine cfcₙ_cases (‖·‖ ≤ c) a f ?_ fun hf hf0 ha ↦ ?_
  · simpa using (norm_nonneg _).trans <| h 0 (quasispectrum.zero_mem 𝕜 a)
  · simp only [← cfcₙ_apply f a, isLUB_le_iff (IsGreatest.norm_cfcₙ f a hf hf0 ha |>.isLUB)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

lemma norm_cfcₙ_le_iff (f : 𝕜 → 𝕜) (a : A) (c : ℝ)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : ‖cfcₙ f a‖ ≤ c ↔ ∀ x ∈ σₙ 𝕜 a, ‖f x‖ ≤ c :=
  ⟨fun h _ hx ↦ norm_apply_le_norm_cfcₙ f a hx hf hf₀ ha |>.trans h, norm_cfcₙ_le⟩

lemma norm_cfcₙ_lt {f : 𝕜 → 𝕜} {a : A} {c : ℝ} (h : ∀ x ∈ σₙ 𝕜 a, ‖f x‖ < c) :
    ‖cfcₙ f a‖ < c := by
  refine cfcₙ_cases (‖·‖ < c) a f ?_ fun hf hf0 ha ↦ ?_
  · simpa using (norm_nonneg _).trans_lt <| h 0 (quasispectrum.zero_mem 𝕜 a)
  · simp only [← cfcₙ_apply f a, (IsGreatest.norm_cfcₙ f a hf hf0 ha |>.lt_iff)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

lemma norm_cfcₙ_lt_iff (f : 𝕜 → 𝕜) (a : A) (c : ℝ)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : ‖cfcₙ f a‖ < c ↔ ∀ x ∈ σₙ 𝕜 a, ‖f x‖ < c :=
  ⟨fun h _ hx ↦ norm_apply_le_norm_cfcₙ f a hx hf hf₀ ha |>.trans_lt h, norm_cfcₙ_lt⟩

open NNReal

lemma nnnorm_cfcₙ_le {f : 𝕜 → 𝕜} {a : A} {c : ℝ≥0} (h : ∀ x ∈ σₙ 𝕜 a, ‖f x‖₊ ≤ c) :
    ‖cfcₙ f a‖₊ ≤ c :=
  norm_cfcₙ_le h

lemma nnnorm_cfcₙ_le_iff (f : 𝕜 → 𝕜) (a : A) (c : ℝ≥0)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : ‖cfcₙ f a‖₊ ≤ c ↔ ∀ x ∈ σₙ 𝕜 a, ‖f x‖₊ ≤ c :=
  norm_cfcₙ_le_iff f a c.1 hf hf₀ ha

lemma nnnorm_cfcₙ_lt {f : 𝕜 → 𝕜} {a : A} {c : ℝ≥0} (h : ∀ x ∈ σₙ 𝕜 a, ‖f x‖₊ < c) :
    ‖cfcₙ f a‖₊ < c :=
  norm_cfcₙ_lt h

lemma nnnorm_cfcₙ_lt_iff (f : 𝕜 → 𝕜) (a : A) (c : ℝ≥0)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : ‖cfcₙ f a‖₊ < c ↔ ∀ x ∈ σₙ 𝕜 a, ‖f x‖₊ < c :=
  norm_cfcₙ_lt_iff f a c.1 hf hf₀ ha

end NormedRing

namespace QuasispectrumRestricts

open NonUnitalIsometricContinuousFunctionalCalculus

variable {R S A : Type*} {p q : A → Prop}

variable [Semifield R] [StarRing R] [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R]

variable [Field S] [StarRing S] [MetricSpace S] [TopologicalRing S] [ContinuousStar S]

variable [NonUnitalRing A] [StarRing A] [Module S A] [IsScalarTower S A A]

variable [SMulCommClass S A A]

variable [Algebra R S] [Module R A] [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S]

variable [IsScalarTower R A A] [SMulCommClass R A A]

variable [MetricSpace A] [NonUnitalIsometricContinuousFunctionalCalculus S A q]

variable [CompleteSpace R] [UniqueNonUnitalContinuousFunctionalCalculus R A]

open scoped NonUnitalContinuousFunctionalCalculus in

protected theorem isometric_cfc (f : C(S, R)) (halg : Isometry (algebraMap R S)) (h0 : p 0)
    (h : ∀ a, p a ↔ q a ∧ QuasispectrumRestricts a f) :
    NonUnitalIsometricContinuousFunctionalCalculus R A p where
  toNonUnitalContinuousFunctionalCalculus := QuasispectrumRestricts.cfc f
    halg.isUniformEmbedding h0 h
  isometric a ha := by
    obtain ⟨ha', haf⟩ := h a |>.mp ha
    have _inst (a : A) : CompactSpace (σₙ R a) := by
      rw [← isCompact_iff_compactSpace, ← quasispectrum.preimage_algebraMap S]
      exact halg.isClosedEmbedding.isCompact_preimage <|
        NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum a
    have := QuasispectrumRestricts.cfc f halg.isUniformEmbedding h0 h
    rw [cfcₙHom_eq_restrict f halg.isUniformEmbedding ha ha' haf]
    refine .of_dist_eq fun g₁ g₂ ↦ ?_
    simp only [nonUnitalStarAlgHom_apply, isometry_cfcₙHom a ha' |>.dist_eq]
    refine le_antisymm ?_ ?_
    all_goals refine ContinuousMap.dist_le dist_nonneg |>.mpr fun x ↦ ?_
    · simpa [halg.dist_eq] using ContinuousMap.dist_apply_le_dist _
    · let x' : σₙ S a := Subtype.map (algebraMap R S) (fun _ ↦ quasispectrum.algebraMap_mem S) x
      apply le_of_eq_of_le ?_ <| ContinuousMap.dist_apply_le_dist x'
      simp only [ContinuousMap.coe_coe, ContinuousMapZero.comp_apply, ContinuousMapZero.coe_mk,
        ContinuousMap.coe_mk, StarAlgHom.ofId_apply, halg.dist_eq, x']
      congr! 2
      all_goals ext; exact haf.left_inv _ |>.symm

end QuasispectrumRestricts

end NonUnital

/-! ### Instances of isometric continuous functional calculi -/

section Instances

section Unital

section Complex

variable {A : Type*} [CStarAlgebra A]

instance IsStarNormal.instIsometricContinuousFunctionalCalculus :
    IsometricContinuousFunctionalCalculus ℂ A IsStarNormal where
  isometric a ha := by
    rw [cfcHom_eq_of_isStarNormal]
    exact isometry_subtype_coe.comp <| StarAlgEquiv.isometry (continuousFunctionalCalculus a)

instance IsSelfAdjoint.instIsometricContinuousFunctionalCalculus :
    IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  SpectrumRestricts.isometric_cfc Complex.reCLM Complex.isometry_ofReal (.zero _)
    fun _ ↦ isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts

end Complex

section NNReal

variable {A : Type*} [NormedRing A] [PartialOrder A] [StarRing A] [StarOrderedRing A]

variable [NormedAlgebra ℝ A] [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

variable [NonnegSpectrumClass ℝ A] [UniqueContinuousFunctionalCalculus ℝ A]

open NNReal in

instance Nonneg.instIsometricContinuousFunctionalCalculus :
    IsometricContinuousFunctionalCalculus ℝ≥0 A (0 ≤ ·) :=
  SpectrumRestricts.isometric_cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    isometry_subtype_coe le_rfl (fun _ ↦ nonneg_iff_isSelfAdjoint_and_spectrumRestricts)

end NNReal

end Unital

section NonUnital

section Complex

variable {A : Type*} [NonUnitalCStarAlgebra A]

open Unitization

open ContinuousMapZero in

instance IsStarNormal.instNonUnitalIsometricContinuousFunctionalCalculus :
    NonUnitalIsometricContinuousFunctionalCalculus ℂ A IsStarNormal where
  isometric a ha := by
    refine AddMonoidHomClass.isometry_of_norm _ fun f ↦ ?_
    rw [← norm_inr (𝕜 := ℂ), ← inrNonUnitalStarAlgHom_apply, ← NonUnitalStarAlgHom.comp_apply,
      inr_comp_cfcₙHom_eq_cfcₙAux a, cfcₙAux]
    simp only [NonUnitalStarAlgHom.comp_assoc, NonUnitalStarAlgHom.comp_apply,
      toContinuousMapHom_apply, NonUnitalStarAlgHom.coe_coe]
    rw [norm_cfcHom (a : Unitization ℂ A), StarAlgEquiv.norm_map]
    rfl

instance IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus :
    NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  QuasispectrumRestricts.isometric_cfc Complex.reCLM Complex.isometry_ofReal (.zero _)
    fun _ ↦ isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts

end Complex

section NNReal

variable {A : Type*} [NonUnitalNormedRing A] [PartialOrder A] [StarRing A] [StarOrderedRing A]

variable [NormedSpace ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]

variable [NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

variable [NonnegSpectrumClass ℝ A] [UniqueNonUnitalContinuousFunctionalCalculus ℝ A]

open NNReal in

instance Nonneg.instNonUnitalIsometricContinuousFunctionalCalculus :
    NonUnitalIsometricContinuousFunctionalCalculus ℝ≥0 A (0 ≤ ·) :=
  QuasispectrumRestricts.isometric_cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    isometry_subtype_coe le_rfl (fun _ ↦ nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts)

end NNReal

end NonUnital

end Instances

/-! ### Properties specific to `ℝ≥0` -/

section NNReal

open NNReal

section Unital

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [PartialOrder A]

variable [StarOrderedRing A] [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

variable [NonnegSpectrumClass ℝ A] [UniqueContinuousFunctionalCalculus ℝ A]

-- CONFLATES (assumes ground = zero): IsGreatest.nnnorm_cfc_nnreal
lemma IsGreatest.nnnorm_cfc_nnreal [Nontrivial A] (f : ℝ≥0 → ℝ≥0) (a : A)
    (hf : ContinuousOn f (σ ℝ≥0 a) := by cfc_cont_tac) (ha : 0 ≤ a := by cfc_tac) :
    IsGreatest (f '' σ ℝ≥0 a) ‖cfc f a‖₊ := by
  rw [cfc_nnreal_eq_real]
  obtain ⟨-, ha'⟩ := nonneg_iff_isSelfAdjoint_and_spectrumRestricts.mp ha
  convert IsGreatest.nnnorm_cfc (fun x : ℝ ↦ (f x.toNNReal : ℝ)) a ?hf_cont
  case hf_cont => exact continuous_subtype_val.comp_continuousOn <|
    ContinuousOn.comp ‹_› continuous_real_toNNReal.continuousOn <| ha'.image ▸ Set.mapsTo_image ..
  ext x
  constructor
  all_goals rintro ⟨x, hx, rfl⟩
  · exact ⟨x, spectrum.algebraMap_mem ℝ hx, by simp⟩
  · exact ⟨x.toNNReal, ha'.apply_mem hx, by simp⟩

lemma apply_le_nnnorm_cfc_nnreal (f : ℝ≥0 → ℝ≥0) (a : A) ⦃x : ℝ≥0⦄ (hx : x ∈ σ ℝ≥0 a)
    (hf : ContinuousOn f (σ ℝ≥0 a) := by cfc_cont_tac) (ha : 0 ≤ a := by cfc_tac) :
    f x ≤ ‖cfc f a‖₊ := by
  revert hx
  nontriviality A
  exact (IsGreatest.nnnorm_cfc_nnreal f a hf ha |>.2 ⟨x, ·, rfl⟩)

lemma nnnorm_cfc_nnreal_le {f : ℝ≥0 → ℝ≥0} {a : A} {c : ℝ≥0} (h : ∀ x ∈ σ ℝ≥0 a, f x ≤ c) :
    ‖cfc f a‖₊ ≤ c := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · rw [Subsingleton.elim (cfc f a) 0]
    simp
  · refine cfc_cases (‖·‖₊ ≤ c) a f (by simp) fun hf ha ↦ ?_
    simp only [← cfc_apply f a, isLUB_le_iff (IsGreatest.nnnorm_cfc_nnreal f a hf ha |>.isLUB)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

lemma nnnorm_cfc_nnreal_le_iff (f : ℝ≥0 → ℝ≥0) (a : A) (c : ℝ≥0)
    (hf : ContinuousOn f (σ ℝ≥0 a) := by cfc_cont_tac)
    (ha : 0 ≤ a := by cfc_tac) : ‖cfc f a‖₊ ≤ c ↔ ∀ x ∈ σ ℝ≥0 a, f x ≤ c :=
  ⟨fun h _ hx ↦ apply_le_nnnorm_cfc_nnreal f a hx hf ha |>.trans h, nnnorm_cfc_nnreal_le⟩

lemma nnnorm_cfc_nnreal_lt {f : ℝ≥0 → ℝ≥0} {a : A} {c : ℝ≥0} (hc : 0 < c)
    (h : ∀ x ∈ σ ℝ≥0 a, f x < c) : ‖cfc f a‖₊ < c := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · rw [Subsingleton.elim (cfc f a) 0]
    simpa
  · refine cfc_cases (‖·‖₊ < c) a f (by simpa) fun hf ha ↦ ?_
    simp only [← cfc_apply f a, (IsGreatest.nnnorm_cfc_nnreal f a hf ha |>.lt_iff)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

lemma nnnorm_cfc_nnreal_lt_iff (f : ℝ≥0 → ℝ≥0) (a : A) {c : ℝ≥0} (hc : 0 < c)
    (hf : ContinuousOn f (σ ℝ≥0 a) := by cfc_cont_tac)
    (ha : 0 ≤ a := by cfc_tac) : ‖cfc f a‖₊ < c ↔ ∀ x ∈ σ ℝ≥0 a, f x < c :=
  ⟨fun h _ hx ↦ apply_le_nnnorm_cfc_nnreal f a hx hf ha |>.trans_lt h, nnnorm_cfc_nnreal_lt hc⟩

end Unital

section NonUnital

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [NormedSpace ℝ A]

variable [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [PartialOrder A]

variable [StarOrderedRing A] [NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

variable [NonnegSpectrumClass ℝ A] [UniqueNonUnitalContinuousFunctionalCalculus ℝ A]

lemma IsGreatest.nnnorm_cfcₙ_nnreal (f : ℝ≥0 → ℝ≥0) (a : A)
    (hf : ContinuousOn f (σₙ ℝ≥0 a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha : 0 ≤ a := by cfc_tac) : IsGreatest (f '' σₙ ℝ≥0 a) ‖cfcₙ f a‖₊ := by
  rw [cfcₙ_nnreal_eq_real]
  obtain ⟨-, ha'⟩ := nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts.mp ha
  convert IsGreatest.nnnorm_cfcₙ (fun x : ℝ ↦ (f x.toNNReal : ℝ)) a ?hf_cont (by simpa)
  case hf_cont => exact continuous_subtype_val.comp_continuousOn <|
    ContinuousOn.comp ‹_› continuous_real_toNNReal.continuousOn <| ha'.image ▸ Set.mapsTo_image ..
  ext x
  constructor
  all_goals rintro ⟨x, hx, rfl⟩
  · exact ⟨x, quasispectrum.algebraMap_mem ℝ hx, by simp⟩
  · exact ⟨x.toNNReal, ha'.apply_mem hx, by simp⟩

lemma apply_le_nnnorm_cfcₙ_nnreal (f : ℝ≥0 → ℝ≥0) (a : A) ⦃x : ℝ≥0⦄ (hx : x ∈ σₙ ℝ≥0 a)
    (hf : ContinuousOn f (σₙ ℝ≥0 a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha : 0 ≤ a := by cfc_tac) : f x ≤ ‖cfcₙ f a‖₊ := by
  revert hx
  exact (IsGreatest.nnnorm_cfcₙ_nnreal f a hf hf0 ha |>.2 ⟨x, ·, rfl⟩)

lemma nnnorm_cfcₙ_nnreal_le {f : ℝ≥0 → ℝ≥0} {a : A} {c : ℝ≥0} (h : ∀ x ∈ σₙ ℝ≥0 a, f x ≤ c) :
    ‖cfcₙ f a‖₊ ≤ c := by
  refine cfcₙ_cases (‖·‖₊ ≤ c) a f (by simp) fun hf hf0 ha ↦ ?_
  simp only [← cfcₙ_apply f a, isLUB_le_iff (IsGreatest.nnnorm_cfcₙ_nnreal f a hf hf0 ha |>.isLUB)]
  rintro - ⟨x, hx, rfl⟩
  exact h x hx

lemma nnnorm_cfcₙ_nnreal_le_iff (f : ℝ≥0 → ℝ≥0) (a : A) (c : ℝ≥0)
    (hf : ContinuousOn f (σₙ ℝ≥0 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : 0 ≤ a := by cfc_tac) : ‖cfcₙ f a‖₊ ≤ c ↔ ∀ x ∈ σₙ ℝ≥0 a, f x ≤ c :=
  ⟨fun h _ hx ↦ apply_le_nnnorm_cfcₙ_nnreal f a hx hf hf₀ ha |>.trans h, nnnorm_cfcₙ_nnreal_le⟩

lemma nnnorm_cfcₙ_nnreal_lt {f : ℝ≥0 → ℝ≥0} {a : A} {c : ℝ≥0} (h : ∀ x ∈ σₙ ℝ≥0 a, f x < c) :
    ‖cfcₙ f a‖₊ < c := by
  refine cfcₙ_cases (‖·‖₊ < c) a f ?_ fun hf hf0 ha ↦ ?_
  · simpa using zero_le (f 0) |>.trans_lt <| h 0 (quasispectrum.zero_mem ℝ≥0 _)
  · simp only [← cfcₙ_apply f a, (IsGreatest.nnnorm_cfcₙ_nnreal f a hf hf0 ha |>.lt_iff)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx

lemma nnnorm_cfcₙ_nnreal_lt_iff (f : ℝ≥0 → ℝ≥0) (a : A) (c : ℝ≥0)
    (hf : ContinuousOn f (σₙ ℝ≥0 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : 0 ≤ a := by cfc_tac) : ‖cfcₙ f a‖₊ < c ↔ ∀ x ∈ σₙ ℝ≥0 a, f x < c :=
  ⟨fun h _ hx ↦ apply_le_nnnorm_cfcₙ_nnreal f a hx hf hf₀ ha |>.trans_lt h, nnnorm_cfcₙ_nnreal_lt⟩

end NonUnital

end NNReal
