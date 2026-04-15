/-
Extracted from Probability/Distributions/Binomial.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Binomial random variables

This file defines the binomial distribution and binomial random variables,
and computes their expectation and variance.

## Main definitions

* `ProbabilityTheory.binomial`:
  Binomial distribution on an arbitrary semiring with parameters `n` and `p`.

## Notation

`Bin(n, p)` is the binomial distribution with parameters `n` and `p` in `ℕ`.
`Bin(R, n, p)` is the binomial distribution with parameters `n` and `p` in `R`.
-/

open MeasureTheory

open scoped NNReal ProbabilityTheory unitInterval

namespace ProbabilityTheory

variable {R Ω : Type*} [MeasurableSpace R] [AddMonoidWithOne R] {m : MeasurableSpace Ω}
  {P : Measure Ω} {X : Ω → R} {n : ℕ} {p : I}

noncomputable def binomial (n : ℕ) (p : I) : Measure ℕ := setBer(Set.Iio n, p).map Set.ncard

scoped notation3 "Bin(" n ", " p ")" => binomial n p

scoped notation3 "Bin(" R ", " n ", " p ")" => (binomial n p).map (Nat.cast : ℕ → R)

-- INSTANCE (free from Core): isProbabilityMeasure_binomial

lemma ae_le_of_hasLaw_binomial {X : Ω → ℕ} (hX : HasLaw X Bin(n, p) P) : ∀ᵐ ω ∂P, X ω ≤ n := by
  rw [hX.ae_iff (p := (· ≤ n)) <| by fun_prop, binomial,
    ae_map_iff (by fun_prop) (Set.finite_Iic _).measurableSet]
  filter_upwards [setBernoulli_ae_subset] with s hs
  simpa using Set.ncard_le_ncard hs

/-! ### Binomial random variables -/

variable {X : Ω → ℝ}

proof_wanted integral_of_hasLaw_binomial (hX : HasLaw X Bin(ℝ, n, p) P) : P[X] = p.val * n

proof_wanted variance_of_hasLaw_binomial (hX : HasLaw X Bin(ℝ, n, p) P) :

    Var[X; P] = p * (1 - p) * n

proof_wanted condVar_of_hasLaw_binomial {m₀ : MeasurableSpace Ω} (hm : m ≤ m₀) {P : Measure[m₀] Ω}

    (hX : HasLaw X Bin(ℝ, n, p) P) :

    Var[X; P | m] =ᵐ[P] P[X | m] * P[1 - X | m]

end ProbabilityTheory
