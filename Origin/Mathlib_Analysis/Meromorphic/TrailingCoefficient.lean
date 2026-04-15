/-
Extracted from Analysis/Meromorphic/TrailingCoefficient.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Trailing Coefficient of a Meromorphic Function

This file defines the trailing coefficient of a meromorphic function. If `f` is meromorphic at a
point `x`, the trailing coefficient is defined as the (unique!) value `g x` for a presentation of
`f` in the form `(z - x) ^ order • g z` with `g` analytic at `x`.

The lemma `MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt` expresses the trailing coefficient
as a limit.
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : 𝕜 → E} {x : 𝕜}

open Filter Topology

variable (f x) in

noncomputable def meromorphicTrailingCoeffAt : E := by
  by_cases h₁ : MeromorphicAt f x
  · by_cases h₂ : meromorphicOrderAt f x = ⊤
    · exact 0
    · exact ((meromorphicOrderAt_ne_top_iff h₁).1 h₂).choose x
  · exact 0
