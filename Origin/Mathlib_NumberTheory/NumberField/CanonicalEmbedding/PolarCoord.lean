/-
Extracted from NumberTheory/NumberField/CanonicalEmbedding/PolarCoord.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Polar coordinate change of variables for the mixed space of a number field

We define two polar coordinate changes of variables for the mixed space `ℝ^r₁ × ℂ^r₂` associated
to a number field `K` of signature `(r₁, r₂)`. The first one is `mixedEmbedding.polarCoord` and has
value in `realMixedSpace K` defined as `ℝ^r₁ × (ℝ ⨯ ℝ)^r₂`, the second is
`mixedEmbedding.polarSpaceCoord` and has value in `polarSpace K` defined as `ℝ^(r₁+r₂) × ℝ^r₂`.

The change of variables with the `polarSpace` is useful to compute the volume of subsets of the
mixed space with enough symmetries, see `volume_eq_two_pi_pow_mul_integral` and
`volume_eq_two_pow_mul_two_pi_pow_mul_integral`

## Main definitions and results

* `mixedEmbedding.polarCoord`: the polar coordinate change of variables between the mixed
  space `ℝ^r₁ × ℂ^r₂` and `ℝ^r₁ × (ℝ × ℝ)^r₂` defined as the identity on the first component and
  mapping `(zᵢ)ᵢ` to `(‖zᵢ‖, Arg zᵢ)ᵢ` on the second component.

* `mixedEmbedding.integral_comp_polarCoord_symm`: the change of variables formula for
  `mixedEmbedding.polarCoord`

* `mixedEmbedding.polarSpaceCoord`: the polar coordinate change of variables between the mixed
  space `ℝ^r₁ × ℂ^r₂` and the polar space `ℝ^(r₁ + r₂) × ℝ^r₂` defined by sending `x` to
  `x w` or `‖x w‖` depending on whether `w` is real or complex for the first component, and
  to `Arg (x w)`, `w` complex, for the second component.

* `mixedEmbedding.integral_comp_polarSpaceCoord_symm`: the change of variables formula for
  `mixedEmbedding.polarSpaceCoord`

* `mixedEmbedding.volume_eq_two_pi_pow_mul_integral`: if the measurable set `A` of the mixed space
  is norm-stable at complex places in the sense that
  `normAtComplexPlaces⁻¹ (normAtComplexPlaces '' A) = A`, then its volume can be computed via an
  integral over `normAtComplexPlaces '' A`.

* `mixedEmbedding.volume_eq_two_pow_mul_two_pi_pow_mul_integral`: if the measurable set `A` of the
  mixed space is norm-stable in the sense that `normAtAllPlaces⁻¹ (normAtAllPlaces '' A) = A`,
  then its volume can be computed via an integral over `normAtAllPlaces '' A`.

-/

variable (K : Type*) [Field K]

namespace NumberField.mixedEmbedding

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding ENNReal MeasureTheory

  MeasureTheory.Measure Real

noncomputable section realMixedSpace

abbrev realMixedSpace :=
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ × ℝ)

noncomputable def mixedSpaceToRealMixedSpace : mixedSpace K ≃ₜ realMixedSpace K :=
  (Homeomorph.refl _).prodCongr <| .piCongrRight fun _ ↦ Complex.equivRealProdCLM.toHomeomorph
