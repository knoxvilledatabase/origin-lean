/-
Extracted from Analysis/Calculus/DSlope.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Slope of a differentiable function

Given a function `f : 𝕜 → E` from a nontrivially normed field to a normed space over this field,
`dslope f a b` is defined as `slope f a b = (b - a)⁻¹ • (f b - f a)` for `a ≠ b` and as `deriv f a`
for `a = b`.

In this file we define `dslope` and prove some basic lemmas about its continuity and
differentiability.
-/

open scoped Topology Filter

open Function Set Filter

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

open Classical in

noncomputable def dslope (f : 𝕜 → E) (a : 𝕜) : 𝕜 → E :=
  update (slope f a) a (deriv f a)
