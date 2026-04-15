/-
Extracted from Probability/Density.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Probability density function

This file defines the probability density function of random variables, by which we mean
measurable functions taking values in a Borel space. The probability density function is defined
as the Radon–Nikodym derivative of the law of `X`. In particular, a measurable function `f`
is said to the probability density function of a random variable `X` if for all measurable
sets `S`, `ℙ(X ∈ S) = ∫ x in S, f x dx`. Probability density functions are one way of describing
the distribution of a random variable, and are useful for calculating probabilities and
finding moments (although the latter is better achieved with moment-generating functions).

This file also defines the continuous uniform distribution and proves some properties about
random variables with this distribution.

## Main definitions

* `MeasureTheory.HasPDF` : A random variable `X : Ω → E` is said to `HasPDF` with
  respect to the measure `ℙ` on `Ω` and `μ` on `E` if the push-forward measure of `ℙ` along `X`
  is absolutely continuous with respect to `μ` and they `HaveLebesgueDecomposition`.
* `MeasureTheory.pdf` : If `X` is a random variable that `HasPDF X ℙ μ`, then `pdf X`
  is the Radon–Nikodym derivative of the push-forward measure of `ℙ` along `X` with respect to `μ`.
* `MeasureTheory.pdf.IsUniform` : A random variable `X` is said to follow the uniform
  distribution if it has a constant probability density function with a compact, non-null support.

## Main results

* `MeasureTheory.pdf.integral_pdf_smul` : Law of the unconscious statistician,
  i.e. if a random variable `X : Ω → E` has pdf `f`, then `𝔼(g(X)) = ∫ x, f x • g x dx` for
  all measurable `g : E → F`.
* `MeasureTheory.pdf.integral_mul_eq_integral` : A real-valued random variable `X` with
  pdf `f` has expectation `∫ x, x * f x dx`.
* `MeasureTheory.pdf.IsUniform.integral_eq` : If `X` follows the uniform distribution with
  its pdf having support `s`, then `X` has expectation `(λ s)⁻¹ * ∫ x in s, x dx` where `λ`
  is the Lebesgue measure.

## TODO

Ultimately, we would also like to define characteristic functions to describe distributions as
it exists for all random variables. However, to define this, we will need Fourier transforms
which we currently do not have.
-/

open scoped MeasureTheory NNReal ENNReal

open TopologicalSpace MeasureTheory Measure ProbabilityTheory

noncomputable section

namespace MeasureTheory

variable {Ω E : Type*} [MeasurableSpace E]

class HasPDF {m : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac) :
    Prop where
  protected aemeasurable' : AEMeasurable X ℙ
  protected haveLebesgueDecomposition' : (map X ℙ).HaveLebesgueDecomposition μ
  protected absolutelyContinuous' : map X ℙ ≪ μ

section HasPDF

variable {_ : MeasurableSpace Ω} {X Y : Ω → E} {ℙ : Measure Ω} {μ : Measure E}

theorem hasPDF_iff :
    HasPDF X ℙ μ ↔ AEMeasurable X ℙ ∧ (map X ℙ).HaveLebesgueDecomposition μ ∧ map X ℙ ≪ μ :=
  ⟨fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

theorem hasPDF_iff_of_aemeasurable (hX : AEMeasurable X ℙ) :
    HasPDF X ℙ μ ↔ (map X ℙ).HaveLebesgueDecomposition μ ∧ map X ℙ ≪ μ := by
  rw [hasPDF_iff]
  simp only [hX, true_and]

variable (X ℙ μ) in
