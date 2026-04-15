/-
Extracted from Topology/ContinuousMap/Bounded/Normed.lean
Genuine: 1 of 4 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Inheritance of normed algebraic structures by bounded continuous functions

For various types of normed algebraic structures `β`, we show in this file that the space of
bounded continuous functions from `α` to `β` inherits the same normed structure, by using
pointwise operations and checking that they are compatible with the uniform distance.
-/

assert_not_exists CStarRing

noncomputable section

open NNReal Set Function

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace BoundedContinuousFunction

section NormedAddCommGroup

variable [TopologicalSpace α] [SeminormedAddCommGroup β]

variable (f g : α →ᵇ β) {x : α} {C : ℝ}

-- INSTANCE (free from Core): instNorm

theorem norm_eq (f : α →ᵇ β) : ‖f‖ = sInf { C : ℝ | 0 ≤ C ∧ ∀ x : α, ‖f x‖ ≤ C } := by
  simp [norm_def, BoundedContinuousFunction.dist_eq]
