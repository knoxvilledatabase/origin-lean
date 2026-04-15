/-
Extracted from MeasureTheory/VectorMeasure/Decomposition/Lebesgue.lean
Genuine: 7 of 12 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Lebesgue decomposition

This file proves the Lebesgue decomposition theorem for signed measures. The Lebesgue decomposition
theorem states that, given two σ-finite measures `μ` and `ν`, there exists a σ-finite measure `ξ`
and a measurable function `f` such that `μ = ξ + fν` and `ξ` is mutually singular with respect
to `ν`.

## Main definitions

* `MeasureTheory.SignedMeasure.HaveLebesgueDecomposition` : A signed measure `s` is said to have
  Lebesgue decomposition with respect to a measure `μ` if both the positive part and negative part
  of `s` have Lebesgue decomposition with respect to `μ`.
* `MeasureTheory.SignedMeasure.singularPart` : The singular part between a signed measure `s`
  and a measure `μ` is simply the singular part of the positive part of `s` with respect to `μ`
  minus the singular part of the negative part of `s` with respect to `μ`.
* `MeasureTheory.SignedMeasure.rnDeriv` : The Radon-Nikodym derivative of a signed
  measure `s` with respect to a measure `μ` is the Radon-Nikodym derivative of the positive part of
  `s` with respect to `μ` minus the Radon-Nikodym derivative of the negative part of `s` with
  respect to `μ`.

## Main results

* `MeasureTheory.SignedMeasure.singularPart_add_withDensity_rnDeriv_eq` :
  the Lebesgue decomposition theorem between a signed measure and a σ-finite positive measure.

## Tags

Lebesgue decomposition theorem
-/

noncomputable section

open scoped MeasureTheory NNReal ENNReal

open Set

variable {α : Type*} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}

namespace MeasureTheory

namespace SignedMeasure

open Measure

class HaveLebesgueDecomposition (s : SignedMeasure α) (μ : Measure α) : Prop where
  posPart : s.toJordanDecomposition.posPart.HaveLebesgueDecomposition μ
  negPart : s.toJordanDecomposition.negPart.HaveLebesgueDecomposition μ

attribute [instance] HaveLebesgueDecomposition.posPart

attribute [instance] HaveLebesgueDecomposition.negPart

theorem not_haveLebesgueDecomposition_iff (s : SignedMeasure α) (μ : Measure α) :
    ¬s.HaveLebesgueDecomposition μ ↔
      ¬s.toJordanDecomposition.posPart.HaveLebesgueDecomposition μ ∨
        ¬s.toJordanDecomposition.negPart.HaveLebesgueDecomposition μ :=
  ⟨fun h => not_or_of_imp fun hp hn => h ⟨hp, hn⟩, fun h hl => (not_and_or.2 h) ⟨hl.1, hl.2⟩⟩

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): haveLebesgueDecomposition_neg

-- INSTANCE (free from Core): haveLebesgueDecomposition_smul

-- INSTANCE (free from Core): haveLebesgueDecomposition_smul_real

def singularPart (s : SignedMeasure α) (μ : Measure α) : SignedMeasure α :=
  (s.toJordanDecomposition.posPart.singularPart μ).toSignedMeasure -
    (s.toJordanDecomposition.negPart.singularPart μ).toSignedMeasure

theorem singularPart_mutuallySingular (s : SignedMeasure α) (μ : Measure α) :
    s.toJordanDecomposition.posPart.singularPart μ ⟂ₘ
      s.toJordanDecomposition.negPart.singularPart μ := by
  by_cases hl : s.HaveLebesgueDecomposition μ
  · obtain ⟨i, hi, hpos, hneg⟩ := s.toJordanDecomposition.mutuallySingular
    rw [s.toJordanDecomposition.posPart.haveLebesgueDecomposition_add μ] at hpos
    rw [s.toJordanDecomposition.negPart.haveLebesgueDecomposition_add μ] at hneg
    rw [add_apply, add_eq_zero] at hpos hneg
    exact ⟨i, hi, hpos.1, hneg.1⟩
  · rw [not_haveLebesgueDecomposition_iff] at hl
    rcases hl with hp | hn
    · rw [Measure.singularPart, dif_neg hp]
      exact MutuallySingular.zero_left
    · rw [Measure.singularPart, Measure.singularPart, dif_neg hn]
      exact MutuallySingular.zero_right

theorem singularPart_totalVariation (s : SignedMeasure α) (μ : Measure α) :
    (s.singularPart μ).totalVariation =
      s.toJordanDecomposition.posPart.singularPart μ +
        s.toJordanDecomposition.negPart.singularPart μ := by
  have :
    (s.singularPart μ).toJordanDecomposition =
      ⟨s.toJordanDecomposition.posPart.singularPart μ,
        s.toJordanDecomposition.negPart.singularPart μ, singularPart_mutuallySingular s μ⟩ := by
    refine JordanDecomposition.toSignedMeasure_injective ?_
    rw [toSignedMeasure_toJordanDecomposition, singularPart, JordanDecomposition.toSignedMeasure]
  rw [totalVariation, this]

nonrec theorem mutuallySingular_singularPart (s : SignedMeasure α) (μ : Measure α) :
    singularPart s μ ⟂ᵥ μ.toENNRealVectorMeasure := by
  rw [mutuallySingular_ennreal_iff, singularPart_totalVariation,
    VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure]
  exact (mutuallySingular_singularPart _ _).add_left (mutuallySingular_singularPart _ _)

end

def rnDeriv (s : SignedMeasure α) (μ : Measure α) : α → ℝ := fun x =>
  (s.toJordanDecomposition.posPart.rnDeriv μ x).toReal -
    (s.toJordanDecomposition.negPart.rnDeriv μ x).toReal

variable {s t : SignedMeasure α}
