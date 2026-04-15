/-
Extracted from Analysis/Normed/Algebra/GelfandFormula.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Gelfand's formula and other results on the spectrum in complex Banach algebras

This file contains results on the spectrum of elements in a complex Banach algebra, including
**Gelfand's formula** and the **Gelfand-Mazur theorem** and the fact that every element in a
complex Banach algebra has nonempty spectrum.

## Main results

* `spectrum.hasDerivAt_resolvent_const_left`: the resolvent function is differentiable on the
  resolvent set.
* `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`: Gelfand's formula for the
  spectral radius in Banach algebras over `ℂ`.
* `spectrum.nonempty`: the spectrum of any element in a complex Banach algebra is nonempty.
* `NormedRing.algEquivComplexOfComplete`: **Gelfand-Mazur theorem** For a complex
  Banach division algebra, the natural `algebraMap ℂ A` is an algebra isomorphism whose inverse
  is given by selecting the (unique) element of `spectrum ℂ a`

## Implementation notes

Note that it is important here that the complex analysis files are privately imported, since the
material proven here gets used in contexts that have nothing to do with complex analysis
(i.e. C⋆-algebras, etc).

-/

variable {𝕜 A : Type*}

open scoped NNReal Topology Ring

open Filter ENNReal

namespace spectrum

section NonTriviallyNormedField

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

theorem hasDerivAt_resolvent_const_left {a : A} {k : 𝕜} (hk : k ∈ resolventSet 𝕜 a) :
    HasDerivAt (resolvent a) (-resolvent a k ^ 2) k := by
  have H₁ : HasFDerivAt Ring.inverse _ (algebraMap 𝕜 A k - a) :=
    hasFDerivAt_ringInverse (𝕜 := 𝕜) hk.unit
  have H₂ : HasDerivAt (fun k => algebraMap 𝕜 A k - a) 1 k := by
    simpa using (Algebra.linearMap 𝕜 A).hasDerivAt.sub_const a
  simpa [resolvent, sq, hk.unit_spec, ← Ring.inverse_unit hk.unit] using H₁.comp_hasDerivAt k H₂
