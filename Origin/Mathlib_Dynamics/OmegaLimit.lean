/-
Extracted from Dynamics/OmegaLimit.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

public meta import Mathlib.Tactic.ToAdditive

/-!
# ω-limits

For a function `ϕ : τ → α → β` where `β` is a topological space, we
define the ω-limit under `ϕ` of a set `s` in `α` with respect to
filter `f` on `τ`: an element `y : β` is in the ω-limit of `s` if the
forward images of `s` intersect arbitrarily small neighbourhoods of
`y` frequently "in the direction of `f`".

In practice `ϕ` is often a continuous monoid-act, but the definition
requires only that `ϕ` has a coercion to the appropriate function
type. In the case where `τ` is `ℕ` or `ℝ` and `f` is `atTop`, we
recover the usual definition of the ω-limit set as the set of all `y`
such that there exist sequences `(tₙ)`, `(xₙ)` such that `ϕ tₙ xₙ ⟶ y`
as `n ⟶ ∞`.

## Notation

The `omegaLimit` scope provides the localised notation `ω` for
`omegaLimit`, as well as `ω⁺` and `ω⁻` for `omegaLimit atTop` and
`omegaLimit atBot` respectively for when the acting monoid is
endowed with an order.
-/

open Set Function Filter Topology

/-!
### Definition and notation
-/

section omegaLimit

variable {τ : Type*} {α : Type*} {β : Type*} {ι : Type*}

def omegaLimit [TopologicalSpace β] (f : Filter τ) (ϕ : τ → α → β) (s : Set α) : Set β :=
  ⋂ u ∈ f, closure (image2 ϕ u s)
