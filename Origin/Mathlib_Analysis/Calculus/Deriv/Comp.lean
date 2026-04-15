/-
Extracted from Analysis/Calculus/Deriv/Comp.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# One-dimensional derivatives of compositions of functions

In this file we prove the chain rule for the following cases:

* `HasDerivAt.comp` etc: `f : 𝕜' → 𝕜'` composed with `g : 𝕜 → 𝕜'`;
* `HasDerivAt.scomp` etc: `f : 𝕜' → E` composed with `g : 𝕜 → 𝕜'`;
* `HasFDerivAt.comp_hasDerivAt` etc: `f : E → F` composed with `g : 𝕜 → E`;

Here `𝕜` is the base normed field, `E` and `F` are normed spaces over `𝕜` and `𝕜'` is an algebra
over `𝕜` (e.g., `𝕜'=𝕜` or `𝕜=ℝ`, `𝕜'=ℂ`).

We also give versions with the `of_eq` suffix, which require an equality proof instead
of definitional equality of the different points used in the composition. These versions are
often more flexible to use.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Keywords

derivative, chain rule
-/

universe u v w

open scoped Topology Filter ENNReal

open Filter Asymptotics Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {f : 𝕜 → F}

variable {f' : F}

variable {x : 𝕜}

variable {s : Set 𝕜}

variable {L : Filter (𝕜 × 𝕜)}

section Composition

/-!
### Derivative of the composition of a vector function and a scalar function

We use `scomp` in lemmas on composition of vector-valued and scalar-valued functions, and `comp`
in lemmas on composition of scalar-valued functions, in analogy for `smul` and `mul` (and also
because the `comp` version with the shorter name will show up much more often in applications).
The formula for the derivative involves `smul` in `scomp` lemmas, which can be reduced to
usual multiplication in `comp` lemmas.
-/

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {s' t' : Set 𝕜'} {h : 𝕜 → 𝕜'} {h₂ : 𝕜' → 𝕜'} {h' h₂' : 𝕜'}
  {g₁ : 𝕜' → F} {g₁' : F} {L' : Filter (𝕜' × 𝕜')} {y : 𝕜'} (x)

theorem HasDerivAtFilter.scomp (hg : HasDerivAtFilter g₁ g₁' L')
    (hh : HasDerivAtFilter h h' L) (hL : Tendsto (Prod.map h h) L L') :
    HasDerivAtFilter (g₁ ∘ h) (h' • g₁') L := by
  simpa using ((hg.hasFDerivAtFilter.restrictScalars 𝕜).comp hh hL).hasDerivAtFilter
