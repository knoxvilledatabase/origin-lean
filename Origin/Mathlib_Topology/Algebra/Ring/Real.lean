/-
Extracted from Topology/Algebra/Ring/Real.lean
Genuine: 4 of 14 | Dissolved: 0 | Infrastructure: 10
-/
import Origin.Core

/-!
# Topological algebra properties of ℝ

This file defines topological field/(semi)ring structures on the
(extended) (nonnegative) reals and shows the algebraic operations are
(uniformly) continuous.

It also includes a bit of more general topological theory of the reals,
needed to define the structures and prove continuity.
-/

assert_not_exists StarRing UniformContinuousConstSMul UniformOnFun

noncomputable section

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

-- INSTANCE (free from Core): :

theorem Real.uniformContinuous_add : UniformContinuous fun p : ℝ × ℝ => p.1 + p.2 :=
  Metric.uniformContinuous_iff.2 fun _ε ε0 =>
    let ⟨δ, δ0, Hδ⟩ := rat_add_continuous_lemma abs ε0
    ⟨δ, δ0, fun _ _ h =>
      let ⟨h₁, h₂⟩ := max_lt_iff.1 h
      Hδ h₁ h₂⟩

theorem Real.uniformContinuous_neg : UniformContinuous (@Neg.neg ℝ _) :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨_, ε0, fun _ _ h => by simpa only [abs_sub_comm, Real.dist_eq, neg_sub_neg] using h⟩

-- INSTANCE (free from Core): :

theorem Real.uniformContinuous_const_mul {x : ℝ} : UniformContinuous (x * ·) :=
  uniformContinuous_of_continuousAt_zero (DistribSMul.toAddMonoidHom ℝ x)
    (continuous_const_smul x).continuousAt

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

namespace EReal

-- INSTANCE (free from Core): :

end EReal

namespace NNReal

/-!
Instances for the following typeclasses are defined:

* `IsTopologicalSemiring ℝ≥0`
* `ContinuousSub ℝ≥0`
* `ContinuousInv₀ ℝ≥0` (continuity of `x⁻¹` away from `0`)
* `ContinuousSMul ℝ≥0 α` (whenever `α` has a continuous `MulAction ℝ α`)

Everything is inherited from the corresponding structures on the reals.
-/

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable {α : Type*}

-- INSTANCE (free from Core): [TopologicalSpace

end NNReal

namespace ENNReal

open Filter NNReal Set Topology

theorem isEmbedding_coe : IsEmbedding ((↑) : ℝ≥0 → ℝ≥0∞) :=
  coe_strictMono.isEmbedding_of_ordConnected <| by rw [range_coe']; exact ordConnected_Iio
