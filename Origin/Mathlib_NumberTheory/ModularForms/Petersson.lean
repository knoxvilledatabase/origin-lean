/-
Extracted from NumberTheory/ModularForms/Petersson.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Petersson scalar product

For `f, f'` functions `ℍ → ℂ`, we define `petersson k f f'` to be the function
`τ ↦ conj (f τ) * f' τ * τ.im ^ k`.

We show this function is (weight 0) invariant under `Γ` if `f, f'` are (weight `k`) invariant under
`Γ`.
-/

open UpperHalfPlane Asymptotics Filter

open scoped MatrixGroups ComplexConjugate ModularForm

namespace UpperHalfPlane

noncomputable def petersson (k : ℤ) (f f' : ℍ → ℂ) (τ : ℍ) :=
  conj (f τ) * f' τ * τ.im ^ k
