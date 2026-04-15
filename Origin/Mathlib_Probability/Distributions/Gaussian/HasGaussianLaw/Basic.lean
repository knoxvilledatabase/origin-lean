/-
Extracted from Probability/Distributions/Gaussian/HasGaussianLaw/Basic.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Gaussian random variables

In this file we prove basic properties of Gaussian random variables.

# Implementation note

Many lemmas are duplicated with an expanded form of some function. For instance there is
`HasGaussianLaw.add` and `HasGaussianLaw.fun_add`. The reason is that if someone wants for instance
to rewrite using `HasGaussianLaw.charFunDual_map_eq` and provide the proof of `HasGaussianLaw`
directly through dot notation, the lemma used must syntactically correspond to the random variable.

## Tags

Gaussian random variable
-/

open MeasureTheory ENNReal WithLp Complex

open scoped RealInnerProductSpace

namespace ProbabilityTheory

variable {Ω E F ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

section Basic

variable [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] [mE : MeasurableSpace E]
  {X Y : Ω → E}

lemma HasGaussianLaw.congr {Y : Ω → E} (hX : HasGaussianLaw X P) (h : X =ᵐ[P] Y) :
    HasGaussianLaw Y P where
  isGaussian_map := by
    rw [← Measure.map_congr h]
    exact hX.isGaussian_map

lemma IsGaussian.hasGaussianLaw [IsGaussian (P.map X)] : HasGaussianLaw X P where
  isGaussian_map := inferInstance

variable {mE} in

lemma IsGaussian.hasGaussianLaw_id {μ : Measure E} [IsGaussian μ] : HasGaussianLaw id μ where
  isGaussian_map := by rwa [Measure.map_id]
