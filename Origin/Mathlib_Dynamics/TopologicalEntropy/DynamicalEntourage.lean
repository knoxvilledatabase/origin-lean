/-
Extracted from Dynamics/TopologicalEntropy/DynamicalEntourage.lean
Genuine: 6 of 8 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Dynamical entourages

Bowen-Dinaburg's definition of topological entropy of a transformation `T` in a metric space
`(X, d)` relies on the so-called dynamical balls. These balls are sets
`B (x, ε, n) = { y | ∀ k < n, d(T^[k] x, T^[k] y) < ε }`.

We implement Bowen-Dinaburg's definitions in the more general context of uniform spaces. Dynamical
balls are replaced by what we call dynamical entourages. This file collects all general lemmas
about these objects.

## Main definitions

- `dynEntourage`: dynamical entourage associated with a given transformation `T`, entourage `U`
  and time `n`.

## Tags

entropy

## TODO

Add product of entourages.

In the context of (pseudo-e)metric spaces, relate the usual definition of dynamical balls with
these dynamical entourages.
-/

namespace Dynamics

open Prod Set UniformSpace

open scoped SetRel Topology Uniformity

variable {X : Type*} {T : X → X} {U V : SetRel X X} {m n : ℕ} {x y : X}

def dynEntourage (T : X → X) (U : SetRel X X) (n : ℕ) : SetRel X X :=
  ⋂ k < n, (map T T)^[k] ⁻¹' U

lemma dynEntourage_eq_inter_Ico (T : X → X) (U : SetRel X X) (n : ℕ) :
    dynEntourage T U n = ⋂ k : Ico 0 n, (map T T)^[k] ⁻¹' U := by
  simp [dynEntourage]

lemma mem_dynEntourage : (x, y) ∈ dynEntourage T U n ↔ ∀ k < n, (T^[k] x, T^[k] y) ∈ U := by
  simp [dynEntourage]

lemma mem_ball_dynEntourage :
    y ∈ ball x (dynEntourage T U n) ↔ ∀ k < n, T^[k] y ∈ ball (T^[k] x) U := by
  simp only [ball, mem_preimage, mem_dynEntourage]

lemma dynEntourage_mem_uniformity [UniformSpace X] (h : UniformContinuous T)
    (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    dynEntourage T U n ∈ 𝓤 X := by
  rw [dynEntourage_eq_inter_Ico T U n]
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [iInter_coe_set, mem_Ico, Nat.zero_le, true_and] at ih ⊢
    rw [Set.biInter_lt_succ]
    apply Filter.inter_mem ih
    rw [map_iterate T T n]
    exact uniformContinuous_def.1 (UniformContinuous.iterate T n h) U U_uni

lemma ball_dynEntourage_mem_nhds [UniformSpace X] (h : Continuous T)
    (U_uni : U ∈ 𝓤 X) (n : ℕ) (x : X) :
    ball x (dynEntourage T U n) ∈ 𝓝 x := by
  rw [dynEntourage_eq_inter_Ico T U n, ball_iInter, Filter.iInter_mem, Subtype.forall]
  intro k _
  simp only [map_iterate, _root_.ball_preimage]
  exact (h.iterate k).continuousAt.preimage_mem_nhds (ball_mem_nhds (T^[k] x) U_uni)

set_option linter.flexible false in -- simp followed by infer_instance

-- INSTANCE (free from Core): isRefl_dynEntourage

set_option linter.flexible false in -- simp followed by infer_instance

-- INSTANCE (free from Core): isSymm_dynEntourage

set_option linter.deprecated false in
