/-
Extracted from Analysis/Analytic/Order.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Vanishing Order of Analytic Functions

This file defines the order of vanishing of an analytic function `f` at a point `z₀`, as an element
of `ℕ∞`.

## TODO

Uniformize API between analytic and meromorphic functions
-/

open Filter Set

open scoped Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
## Vanishing Order at a Point: Definition and Characterization
-/

section NormedSpace

variable {f g : 𝕜 → E} {n : ℕ} {z₀ : 𝕜}

open scoped Classical in

noncomputable def analyticOrderAt (f : 𝕜 → E) (z₀ : 𝕜) : ℕ∞ :=
  if hf : AnalyticAt 𝕜 f z₀ then
    if h : ∀ᶠ z in 𝓝 z₀, f z = 0 then ⊤
    else ↑(hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h).choose
  else 0

noncomputable def analyticOrderNatAt (f : 𝕜 → E) (z₀ : 𝕜) : ℕ := (analyticOrderAt f z₀).toNat
