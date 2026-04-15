/-
Extracted from Analysis/Fourier/AddCircle.lean
Genuine: 3 of 6 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!

# Fourier analysis on the additive circle

This file contains basic results on Fourier series for functions on the additive circle
`AddCircle T = ℝ / ℤ • T`.

## Main definitions

* `haarAddCircle`, Haar measure on `AddCircle T`, normalized to have total measure `1`.
  Note that this is not the same normalisation
  as the standard measure defined in `IntervalIntegral.Periodic`,
  so we do not declare it as a `MeasureSpace` instance, to avoid confusion.
* for `n : ℤ`, `fourier n` is the monomial `fun x => exp (2 π i n x / T)`,
  bundled as a continuous map from `AddCircle T` to `ℂ`.
* `fourierBasis` is the Hilbert basis of `Lp ℂ 2 haarAddCircle` given by the images of the
  monomials `fourier n`.
* `fourierCoeff f n`, for `f : AddCircle T → E` (with `E` a complete normed `ℂ`-vector space), is
  the `n`-th Fourier coefficient of `f`, defined as an integral over `AddCircle T`. The lemma
  `fourierCoeff_eq_intervalIntegral` expresses this as an integral over `[a, a + T]` for any real
  `a`.
* `fourierCoeffOn`, for `f : ℝ → E` and `a < b` reals, is the `n`-th Fourier
  coefficient of the unique periodic function of period `b - a` which agrees with `f` on `(a, b]`.
  The lemma `fourierCoeffOn_eq_integral` expresses this as an integral over `[a, b]`.

## Main statements

The theorem `span_fourier_closure_eq_top` states that the span of the monomials `fourier n` is
dense in `C(AddCircle T, ℂ)`, i.e. that its `Submodule.topologicalClosure` is `⊤`.  This follows
from the Stone-Weierstrass theorem after checking that the span is a subalgebra, is closed under
conjugation, and separates points.

Using this and general theory on approximation of Lᵖ functions by continuous functions, we deduce
(`span_fourierLp_closure_eq_top`) that for any `1 ≤ p < ∞`, the span of the Fourier monomials is
dense in the Lᵖ space of `AddCircle T`. For `p = 2` we show (`orthonormal_fourier`) that the
monomials are also orthonormal, so they form a Hilbert basis for L², which is named as
`fourierBasis`; in particular, for `L²` functions `f`, the Fourier series of `f` converges to `f`
in the `L²` topology (`hasSum_fourier_series_L2`). Parseval's identity, `hasSum_sq_fourierCoeff`, is
a direct consequence.

For continuous maps `f : AddCircle T → ℂ`, the theorem
`hasSum_fourier_series_of_summable` states that if the sequence of Fourier
coefficients of `f` is summable, then the Fourier series `∑ (i : ℤ), fourierCoeff f i * fourier i`
converges to `f` in the uniform-convergence topology of `C(AddCircle T, ℂ)`.
-/

noncomputable section

open scoped ENNReal ComplexConjugate Real

open TopologicalSpace ContinuousMap MeasureTheory MeasureTheory.Measure Algebra Submodule Set

variable {T : ℝ}

namespace AddCircle

/-! ### Measure on `AddCircle T`

In this file we use the Haar measure on `AddCircle T` normalised to have total measure 1 (which is
**not** the same as the standard measure defined in `Topology.Instances.AddCircle`). -/

variable [hT : Fact (0 < T)]

def haarAddCircle : Measure (AddCircle T) :=
  addHaarMeasure ⊤

deriving IsAddHaarMeasure

-- INSTANCE (free from Core): :

lemma integral_haarAddCircle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : AddCircle T → E} : ∫ t, f t ∂haarAddCircle = T⁻¹ • ∫ t, f t := by
  rw [volume_eq_smul_haarAddCircle, integral_smul_measure, ENNReal.toReal_ofReal hT.out.le,
    inv_smul_smul₀ hT.out.ne']

end AddCircle

namespace MeasureTheory

alias ⟨MemLp.of_haarAddCircle, MemLp.haarAddCircle⟩ := memLp_haarAddCircle_iff

end MeasureTheory

open AddCircle

section Monomials

def fourier (n : ℤ) : C(AddCircle T, ℂ) where
  toFun x := toCircle (n • x :)
  continuous_toFun := continuous_induced_dom.comp <| continuous_toCircle.comp <| continuous_zsmul _
