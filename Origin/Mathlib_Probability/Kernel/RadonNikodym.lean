/-
Extracted from Probability/Kernel/RadonNikodym.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Radon-Nikodym derivative and Lebesgue decomposition for kernels

Let `α` and `γ` be two measurable spaces, where either `α` is countable or `γ` is
countably generated. Let `κ, η : Kernel α γ` be finite kernels.
Then there exists a function `Kernel.rnDeriv κ η : α → γ → ℝ≥0∞` jointly measurable on `α × γ`
and a kernel `Kernel.singularPart κ η : Kernel α γ` such that
* `κ = Kernel.withDensity η (Kernel.rnDeriv κ η) + Kernel.singularPart κ η`,
* for all `a : α`, `Kernel.singularPart κ η a ⟂ₘ η a`,
* for all `a : α`, `Kernel.singularPart κ η a = 0 ↔ κ a ≪ η a`,
* for all `a : α`, `Kernel.withDensity η (Kernel.rnDeriv κ η) a = 0 ↔ κ a ⟂ₘ η a`.

Furthermore, the sets `{a | κ a ≪ η a}` and `{a | κ a ⟂ₘ η a}` are measurable.

When `γ` is countably generated, the construction of the derivative starts from `Kernel.density`:
for two finite kernels `κ' : Kernel α (γ × β)` and `η' : Kernel α γ` with `fst κ' ≤ η'`,
the function `density κ' η' : α → γ → Set β → ℝ` is jointly measurable in the first two arguments
and satisfies that for all `a : α` and all measurable sets `s : Set β` and `A : Set γ`,
`∫ x in A, density κ' η' a x s ∂(η' a) = (κ' a (A ×ˢ s)).toReal`.
We use that definition for `β = Unit` and `κ' = map κ (fun a ↦ (a, ()))`. We can't choose `η' = η`
in general because we might not have `κ ≤ η`, but if we could, we would get a measurable function
`f` with the property `κ = withDensity η f`, which is the decomposition we want for `κ ≤ η`.
To circumvent that difficulty, we take `η' = κ + η` and thus define `rnDerivAux κ η`.
Finally, `rnDeriv κ η a x` is given by
`ENNReal.ofReal (rnDerivAux κ (κ + η) a x) / ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a x)`.
Up to some conversions between `ℝ` and `ℝ≥0`, the singular part is
`withDensity (κ + η) (rnDerivAux κ (κ + η) - (1 - rnDerivAux κ (κ + η)) * rnDeriv κ η)`.

The countably generated measurable space assumption is not needed to have a decomposition for
measures, but the additional difficulty with kernels is to obtain joint measurability of the
derivative. This is why we can't simply define `rnDeriv κ η` by `a ↦ (κ a).rnDeriv (ν a)`
everywhere unless `α` is countable (although `rnDeriv κ η` has that value almost everywhere).
See the construction of `Kernel.density` for details on how the countably generated hypothesis
is used.

## Main definitions

* `ProbabilityTheory.Kernel.rnDeriv`: a function `α → γ → ℝ≥0∞` jointly measurable on `α × γ`
* `ProbabilityTheory.Kernel.singularPart`: a `Kernel α γ`

## Main statements

* `ProbabilityTheory.Kernel.mutuallySingular_singularPart`: for all `a : α`,
  `Kernel.singularPart κ η a ⟂ₘ η a`
* `ProbabilityTheory.Kernel.rnDeriv_add_singularPart`:
  `Kernel.withDensity η (Kernel.rnDeriv κ η) + Kernel.singularPart κ η = κ`
* `ProbabilityTheory.Kernel.measurableSet_absolutelyContinuous` : the set `{a | κ a ≪ η a}`
  is Measurable
* `ProbabilityTheory.Kernel.measurableSet_mutuallySingular` : the set `{a | κ a ⟂ₘ η a}`
  is Measurable

Uniqueness results: if `κ = η.withDensity f + ξ` for measurable `f` and `ξ` is such that
`ξ a ⟂ₘ η a` for some `a : α` then
* `ProbabilityTheory.Kernel.eq_rnDeriv`: `f a =ᵐ[η a] Kernel.rnDeriv κ η a`
* `ProbabilityTheory.Kernel.eq_singularPart`: `ξ a = Kernel.singularPart κ η a`

## References

Theorem 1.28 in [O. Kallenberg, Random Measures, Theory and Applications][kallenberg2017].

-/

open MeasureTheory Set Filter ENNReal

open scoped NNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α γ : Type*} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ} {κ η : Kernel α γ}
  [hαγ : MeasurableSpace.CountableOrCountablyGenerated α γ]

open Classical in

noncomputable

def rnDerivAux (κ η : Kernel α γ) (a : α) (x : γ) : ℝ :=
  if hα : Countable α then ((κ a).rnDeriv (η a) x).toReal
  else haveI := hαγ.countableOrCountablyGenerated.resolve_left hα
    density (map κ (fun a ↦ (a, ()))) η a x univ

lemma rnDerivAux_nonneg (hκη : κ ≤ η) {a : α} {x : γ} : 0 ≤ rnDerivAux κ η a x := by
  rw [rnDerivAux]
  split_ifs with hα
  · exact ENNReal.toReal_nonneg
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    exact density_nonneg ((fst_map_id_prod _ measurable_const).trans_le hκη) _ _ _

lemma rnDerivAux_le_one [IsFiniteKernel η] (hκη : κ ≤ η) {a : α} :
    rnDerivAux κ η a ≤ᵐ[η a] 1 := by
  filter_upwards [Measure.rnDeriv_le_one_of_le (hκη a)] with x hx_le_one
  simp_rw [rnDerivAux]
  split_ifs with hα
  · refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simp only [Pi.one_apply, ENNReal.ofReal_one]
    exact hx_le_one
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    exact density_le_one ((fst_map_id_prod _ measurable_const).trans_le hκη) _ _ _
