/-
Extracted from Dynamics/TopologicalEntropy/DynamicalEntourage.lean
Genuine: 11 of 11 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Topology.UniformSpace.Basic

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
Once #PR14718 has passed, add product of entourages.

In the context of (pseudo-e)metric spaces, relate the usual definition of dynamical balls with
these dynamical entourages.
-/

namespace Dynamics

open Prod Set Uniformity UniformSpace

variable {X : Type*}

def dynEntourage (T : X → X) (U : Set (X × X)) (n : ℕ) : Set (X × X) :=
  ⋂ k < n, (map T T)^[k] ⁻¹' U

lemma dynEntourage_eq_inter_Ico (T : X → X) (U : Set (X × X)) (n : ℕ) :
    dynEntourage T U n = ⋂ k : Ico 0 n, (map T T)^[k] ⁻¹' U := by
  simp [dynEntourage]

lemma mem_dynEntourage {T : X → X} {U : Set (X × X)} {n : ℕ} {x y : X} :
    (x, y) ∈ dynEntourage T U n ↔ ∀ k < n, (T^[k] x, T^[k] y) ∈ U := by
  simp [dynEntourage]

lemma mem_ball_dynEntourage {T : X → X} {U : Set (X × X)} {n : ℕ} {x y : X} :
    y ∈ ball x (dynEntourage T U n) ↔ ∀ k < n, T^[k] y ∈ ball (T^[k] x) U := by
  simp only [ball, mem_preimage]; exact mem_dynEntourage

lemma dynEntourage_mem_uniformity [UniformSpace X] {T : X → X} (h : UniformContinuous T)
    {U : Set (X × X)} (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    dynEntourage T U n ∈ 𝓤 X := by
  rw [dynEntourage_eq_inter_Ico T U n]
  refine Filter.iInter_mem.2 fun k ↦ ?_
  rw [map_iterate T T k]
  exact uniformContinuous_def.1 (UniformContinuous.iterate T k h) U U_uni

lemma idRel_subset_dynEntourage (T : X → X) {U : Set (X × X)} (h : idRel ⊆ U) (n : ℕ) :
    idRel ⊆ (dynEntourage T U n) := by
  simp only [dynEntourage, map_iterate, subset_iInter_iff, idRel_subset, mem_preimage, map_apply]
  exact fun _ _ _ ↦ h rfl

lemma _root_.SymmetricRel.dynEntourage (T : X → X) {U : Set (X × X)} (h : SymmetricRel U) (n : ℕ) :
    SymmetricRel (dynEntourage T U n) := by
  ext xy
  simp only [Dynamics.dynEntourage, map_iterate, mem_preimage, mem_iInter]
  refine forall₂_congr fun k _ ↦ ?_
  exact map_apply' _ _ _ ▸ SymmetricRel.mk_mem_comm h

lemma dynEntourage_comp_subset (T : X → X) (U V : Set (X × X)) (n : ℕ) :
    (dynEntourage T U n) ○ (dynEntourage T V n) ⊆ dynEntourage T (U ○ V) n := by
  simp only [dynEntourage, map_iterate, subset_iInter_iff]
  intro k k_n xy xy_comp
  simp only [compRel, mem_iInter, mem_preimage, map_apply, mem_setOf_eq] at xy_comp ⊢
  rcases xy_comp with ⟨z, hz1, hz2⟩
  exact mem_ball_comp (hz1 k k_n) (hz2 k k_n)

lemma _root_.isOpen.dynEntourage [TopologicalSpace X] {T : X → X} (T_cont : Continuous T)
    {U : Set (X × X)} (U_open : IsOpen U) (n : ℕ) :
    IsOpen (dynEntourage T U n) := by
  rw [dynEntourage_eq_inter_Ico T U n]
  refine isOpen_iInter_of_finite fun k ↦ ?_
  exact U_open.preimage ((T_cont.prodMap T_cont).iterate k)

lemma dynEntourage_monotone (T : X → X) (n : ℕ) :
    Monotone (fun U : Set (X × X) ↦ dynEntourage T U n) :=
  fun _ _ h ↦ iInter₂_mono fun _ _ ↦ preimage_mono h

lemma dynEntourage_antitone (T : X → X) (U : Set (X × X)) :
    Antitone (fun n : ℕ ↦ dynEntourage T U n) :=
  fun m n m_n ↦ iInter₂_mono' fun k k_m ↦ by use k, lt_of_lt_of_le k_m m_n
