/-
Extracted from Analysis/Calculus/Deriv/Prod.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Derivatives of functions taking values in product types

In this file we prove lemmas about derivatives of functions `f : 𝕜 → E × F` and of functions
`f : 𝕜 → (Π i, E i)`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Keywords

derivative
-/

universe u v w

open Topology Filter Asymptotics Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {f₁ : 𝕜 → F} {f₁' : F} {x : 𝕜} {s : Set 𝕜} {L : Filter (𝕜 × 𝕜)}

section CartesianProduct

/-! ### Derivative of the Cartesian product of two functions -/

variable {G : Type w} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable {f₂ : 𝕜 → G} {f₂' : G}

theorem HasDerivAtFilter.prodMk (hf₁ : HasDerivAtFilter f₁ f₁' L)
    (hf₂ : HasDerivAtFilter f₂ f₂' L) : HasDerivAtFilter (fun x => (f₁ x, f₂ x)) (f₁', f₂') L :=
  HasFDerivAtFilter.prodMk hf₁ hf₂

theorem HasDerivWithinAt.prodMk (hf₁ : HasDerivWithinAt f₁ f₁' s x)
    (hf₂ : HasDerivWithinAt f₂ f₂' s x) : HasDerivWithinAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') s x :=
  HasDerivAtFilter.prodMk hf₁ hf₂

theorem HasDerivAt.prodMk (hf₁ : HasDerivAt f₁ f₁' x) (hf₂ : HasDerivAt f₂ f₂' x) :
    HasDerivAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') x :=
  HasDerivAtFilter.prodMk hf₁ hf₂

theorem HasStrictDerivAt.prodMk (hf₁ : HasStrictDerivAt f₁ f₁' x)
    (hf₂ : HasStrictDerivAt f₂ f₂' x) : HasStrictDerivAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') x :=
  HasDerivAtFilter.prodMk hf₁ hf₂

end CartesianProduct

section Pi

/-! ### Derivatives of functions `f : 𝕜 → Π i, E i` -/

variable {ι : Type*} {E' : ι → Type*} [∀ i, NormedAddCommGroup (E' i)]
  [∀ i, NormedSpace 𝕜 (E' i)] {φ : 𝕜 → ∀ i, E' i} {φ' : ∀ i, E' i}
