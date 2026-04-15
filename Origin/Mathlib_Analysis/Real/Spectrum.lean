/-
Extracted from Analysis/Real/Spectrum.lean
Genuine: 10 of 11 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Some lemmas on the spectrum and quasispectrum of elements and positivity

-/

namespace SpectrumRestricts

open NNReal ENNReal

variable {A : Type*} [Ring A] [Algebra ℝ A]

lemma nnreal_of_nonneg [PartialOrder A] [NonnegSpectrumClass ℝ A] {a : A} (ha : 0 ≤ a) :
    SpectrumRestricts a ContinuousMap.realToNNReal :=
  nnreal_iff.mpr <| spectrum_nonneg_of_nonneg ha

lemma nnreal_le_iff {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ spectrum ℝ≥0 a, r ≤ x) ↔ ∀ x ∈ spectrum ℝ a, r ≤ x := by
  simp [← ha.algebraMap_image]

lemma nnreal_lt_iff {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ spectrum ℝ≥0 a, r < x) ↔ ∀ x ∈ spectrum ℝ a, r < x := by
  simp [← ha.algebraMap_image]

lemma le_nnreal_iff {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ spectrum ℝ≥0 a, x ≤ r) ↔ ∀ x ∈ spectrum ℝ a, x ≤ r := by
  simp [← ha.algebraMap_image]

lemma lt_nnreal_iff {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ spectrum ℝ≥0 a, x < r) ↔ ∀ x ∈ spectrum ℝ a, x < r := by
  simp [← ha.algebraMap_image]

end SpectrumRestricts

namespace QuasispectrumRestricts

open NNReal ENNReal

local notation "σₙ" => quasispectrum

variable {A : Type*} [NonUnitalRing A]

lemma nnreal_iff [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] {a : A} :
    QuasispectrumRestricts a ContinuousMap.realToNNReal ↔ ∀ x ∈ σₙ ℝ a, 0 ≤ x := by
  rw [quasispectrumRestricts_iff_spectrumRestricts_inr,
    Unitization.quasispectrum_eq_spectrum_inr' _ ℝ, SpectrumRestricts.nnreal_iff]

lemma nnreal_of_nonneg [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [PartialOrder A]
    [NonnegSpectrumClass ℝ A] {a : A} (ha : 0 ≤ a) :
    QuasispectrumRestricts a ContinuousMap.realToNNReal :=
  nnreal_iff.mpr <| quasispectrum_nonneg_of_nonneg _ ha

lemma le_nnreal_iff [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] {a : A}
    (ha : QuasispectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ quasispectrum ℝ≥0 a, x ≤ r) ↔ ∀ x ∈ quasispectrum ℝ a, x ≤ r := by
  simp [← ha.algebraMap_image]

lemma lt_nnreal_iff [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] {a : A}
    (ha : QuasispectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ quasispectrum ℝ≥0 a, x < r) ↔ ∀ x ∈ quasispectrum ℝ a, x < r := by
  simp [← ha.algebraMap_image]

end QuasispectrumRestricts

variable {A : Type*} [Ring A] [PartialOrder A]

open scoped NNReal

lemma coe_mem_spectrum_real_of_nonneg [Algebra ℝ A] [NonnegSpectrumClass ℝ A] {a : A} {x : ℝ≥0}
    (ha : 0 ≤ a := by cfc_tac) :
    (x : ℝ) ∈ spectrum ℝ a ↔ x ∈ spectrum ℝ≥0 a := by
  simp [← (SpectrumRestricts.nnreal_of_nonneg ha).algebraMap_image, Set.mem_image,
    NNReal.algebraMap_eq_coe]
