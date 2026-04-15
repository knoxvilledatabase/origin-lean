/-
Extracted from Analysis/Normed/Algebra/Spectrum.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The spectrum of elements in a complete normed algebra

This file contains the basic theory for the resolvent and spectrum of a Banach algebra.
Theorems specific to *complex* Banach algebras, such as *Gelfand's formula* can be found in
 `Mathlib/Analysis/Normed/Algebra/GelfandFormula.lean`.

## Main definitions

* `spectralRadius : ℝ≥0∞`: supremum of `‖k‖₊` for all `k ∈ spectrum 𝕜 a`

## Main statements

* `spectrum.isOpen_resolventSet`: the resolvent set is open.
* `spectrum.isClosed`: the spectrum is closed.
* `spectrum.subset_closedBall_norm`: the spectrum is a subset of closed disk of radius
  equal to the norm.
* `spectrum.isCompact`: the spectrum is compact.
* `spectrum.spectralRadius_le_nnnorm`: the spectral radius is bounded above by the norm.

-/

assert_not_exists ProbabilityTheory.cond

assert_not_exists HasFDerivAt

open NormedSpace Topology -- For `NormedSpace.exp`.

open scoped ENNReal NNReal

noncomputable def spectralRadius (𝕜 : Type*) {A : Type*} [NormedField 𝕜] [Ring A] [Algebra 𝕜 A]
    (a : A) : ℝ≥0∞ :=
  ⨆ k ∈ spectrum 𝕜 a, ‖k‖₊

variable {𝕜 : Type*} {A : Type*}

namespace spectrum

section SpectrumCompact

open Filter

variable [NormedField 𝕜]

local notation "σ" => spectrum 𝕜

local notation "ρ" => resolventSet 𝕜

local notation "↑ₐ" => algebraMap 𝕜 A

section Algebra

variable [Ring A] [Algebra 𝕜 A]
