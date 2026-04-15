/-
Extracted from NumberTheory/ModularForms/JacobiTheta/Manifold.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Manifold differentiability of the Jacobi theta function

In this file we reformulate differentiability of the Jacobi theta function in terms of manifold
differentiability.

## TODO

Prove smoothness (in terms of `Smooth`).
-/

open scoped UpperHalfPlane Manifold

theorem mdifferentiable_jacobiTheta : MDiff (jacobiTheta ∘ (↑) : ℍ → ℂ) :=
  fun τ => (differentiableAt_jacobiTheta τ.2).mdifferentiableAt.comp τ τ.mdifferentiable_coe
