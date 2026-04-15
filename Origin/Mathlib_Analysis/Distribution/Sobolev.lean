/-
Extracted from Analysis/Distribution/Sobolev.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Sobolev spaces (Bessel potential spaces)

In this file we define Sobolev spaces on normed vector spaces via the Fourier transform.
These spaces are also known as Bessel potential spaces. The Bessel potential operator
`besselPotential` is the Fourier multiplier with the symbol `x ↦ (1 + ‖x‖ ^ 2) ^ (s / 2)` and a
tempered distribution `u` belongs to the Sobolev space `H ^ {s, p}` if
`besselPotential E F s u` can be represented by a `Lp` function, informally this is written as
`𝓕⁻ (fun x ↦ (1 + ‖x‖ ^ 2) ^ (s / 2)) 𝓕 u ∈ Lp`.

Note that the Bessel potential is the operator `(1 - (2 * π) ^ (-2) • Δ) ^ (s / 2)` and not
`(1 - Δ) ^ (s / 2)` due to the convention of the Fourier transform. This obviously does not impact
the definition of the Sobolev spaces.

## Main definitions

* `TemperedDistribution.besselPotential`: The Bessel potential operator is the Fourier multiplier
  with the function `(1 + ‖x‖ ^ 2) ^ (s / 2)`.
* `TemperedDistribution.memSobolev`: A tempered distribution lies in the Sobolev space of order `s`
  and `p` if `besselPotential E F s u ∈ Lp`.

## Main statements

* `SchwartzMap.memSobolev`: Each Schwartz function belongs to every Sobolev space
* `TemperedDistribution.memSobolev_two_iff_fourier`: The characterization of `p = 2` Sobolev
  functions
* `TemperedDistribution.MemSobolev.fourierMultiplierCLM_of_bounded`: If `u` is a Sobolev
  function, then `g • u` is a Sobolev function of the same order provided `g` is bounded.
* `TemperedDistribution.MemSobolev.lineDerivOp`: If `u` is a Sobolev function of order `s`, then
  `∂_{m} u` is a Sobolev function of order `s - 1`.
* `TemperedDistribution.MemSobolev.laplacian`: If `u` is a Sobolev function of order `s`, then
  `Δ u` is a Sobolev function of order `s - 2`.


## References
* [M. Taylor, *Partial Differential Equations 1*][taylorPDE1]
* [W. McLean, *Strongly Elliptic Systems and Boundary Integral Equations][mclean2000]

-/

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open FourierTransform TemperedDistribution ENNReal MeasureTheory

open scoped SchwartzMap

namespace TemperedDistribution

section normed

variable [NormedSpace ℂ F]

variable (E F) in

def besselPotential (s : ℝ) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  fourierMultiplierCLM F (fun x ↦ ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ))

variable (E F) in
