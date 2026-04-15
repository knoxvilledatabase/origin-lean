/-
Extracted from Analysis/Convex/Strong.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Uniformly and strongly convex functions

In this file, we define uniformly convex functions and strongly convex functions.

For a real normed space `E`, a uniformly convex function with modulus `φ : ℝ → ℝ` is a function
`f : E → ℝ` such that `f (t • x + (1 - t) • y) ≤ t • f x + (1 - t) • f y - t * (1 - t) * φ ‖x - y‖`
for all `t ∈ [0, 1]`.

A `m`-strongly convex function is a uniformly convex function with modulus `fun r ↦ m / 2 * r ^ 2`.
If `E` is an inner product space, this is equivalent to `x ↦ f x - m / 2 * ‖x‖ ^ 2` being convex.

## TODO

Prove derivative properties of strongly convex functions.
-/

open Real

variable {E : Type*} [NormedAddCommGroup E]

section NormedSpace

variable [NormedSpace ℝ E] {φ ψ : ℝ → ℝ} {s : Set E} {m : ℝ} {f g : E → ℝ}

def UniformConvexOn (s : Set E) (φ : ℝ → ℝ) (f : E → ℝ) : Prop :=
  Convex ℝ s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • x + b • y) ≤ a • f x + b • f y - a * b * φ ‖x - y‖

def UniformConcaveOn (s : Set E) (φ : ℝ → ℝ) (f : E → ℝ) : Prop :=
  Convex ℝ s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    a • f x + b • f y + a * b * φ ‖x - y‖ ≤ f (a • x + b • y)
