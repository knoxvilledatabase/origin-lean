/-
Extracted from Analysis/Meromorphic/Order.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Orders of Meromorphic Functions

This file defines the order of a meromorphic function `f` at a point `z₀`, as an element of
`ℤ ∪ {∞}`.

We characterize the order being `< 0`, or `= 0`, or `> 0`, as the convergence of the function
to infinity, resp. a nonzero constant, resp. zero.

## TODO

Uniformize API between analytic and meromorphic functions
-/

open Filter Set WithTop.LinearOrderedAddCommGroup

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f f₁ f₂ : 𝕜 → E} {x : 𝕜}

/-!
## Order at a Point: Definition and Characterization
-/

open scoped Classical in

noncomputable def meromorphicOrderAt (f : 𝕜 → E) (x : 𝕜) : WithTop ℤ :=
  if hf : MeromorphicAt f x then
    ((analyticOrderAt (fun z ↦ (z - x) ^ hf.choose • f z) x).map (↑· : ℕ → ℤ)) - hf.choose
  else 0
