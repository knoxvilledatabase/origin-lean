/-
Extracted from Analysis/FunctionalSpaces/SobolevInequality.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Gagliardo-Nirenberg-Sobolev inequality

In this file we prove the Gagliardo-Nirenberg-Sobolev inequality.
This states that for compactly supported `C¹`-functions between finite-dimensional vector spaces,
we can bound the `L^p`-norm of `u` by the `L^q` norm of the derivative of `u`.
The bound is up to a constant that is independent of the function `u`.
Let `n` be the dimension of the domain.

The main step in the proof, which we dubbed the "grid-lines lemma" below, is a complicated
inductive argument that involves manipulating an `n+1`-fold iterated integral and a product of
`n+2` factors. In each step, one pushes one of the integral inside (all but one of)
the factors of the product using Hölder's inequality. The precise formulation of the induction
hypothesis (`MeasureTheory.GridLines.T_insert_le_T_lmarginal_singleton`) is tricky,
and none of the 5 sources we referenced stated it.

In the formalization we use the operation `MeasureTheory.lmarginal` to work with the iterated
integrals, and use `MeasureTheory.lmarginal_insert'` to conveniently push one of the integrals
inside. The Hölder's inequality step is done using `ENNReal.lintegral_mul_prod_norm_pow_le`.

The conclusions of the main results below are an estimation up to a constant multiple.
We don't really care about this constant, other than that it only depends on some pieces of data,
typically `E`, `μ`, `p` and sometimes also the codomain of `u` or the support of `u`.
We state these constants as separate definitions.

## Main results

* `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`:
  The bound holds for `1 ≤ p`, `0 < n` and `q⁻¹ = p⁻¹ - n⁻¹`
* `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_le`:
  The bound holds when `1 ≤ p < n`, `0 ≤ q` and `p⁻¹ - n⁻¹ ≤ q⁻¹`.
  Note that in this case the constant depends on the support of `u`.

Potentially also useful:
* `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one`: this is the inequality for `q = 1`.
  In this version, the codomain can be an arbitrary Banach space.
* `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq_inner`: in this version,
  the codomain is assumed to be a Hilbert space, without restrictions on its dimension.
-/

open scoped ENNReal NNReal

open Set Function Finset MeasureTheory Measure Filter

noncomputable section

variable {ι : Type*}

local prefix:max "#" => Fintype.card

/-! ## The grid-lines lemma -/

variable {A : ι → Type*} [∀ i, MeasurableSpace (A i)]
  (μ : ∀ i, Measure (A i))

namespace MeasureTheory

section DecidableEq

variable [DecidableEq ι]

namespace GridLines

def T (p : ℝ) (f : (∀ i, A i) → ℝ≥0∞) (s : Finset ι) : (∀ i, A i) → ℝ≥0∞ :=
  ∫⋯∫⁻_s, f ^ (1 - (s.card - 1 : ℝ) * p) * ∏ i ∈ s, (∫⋯∫⁻_{i}, f ∂μ) ^ p ∂μ

variable {p : ℝ}
