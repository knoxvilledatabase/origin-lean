/-
Extracted from Topology/MetricSpace/Pseudo/Pi.lean
Genuine: 9 of 12 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Product of pseudometric spaces

This file constructs the infinity distance on finite products of pseudometric spaces.
-/

open Bornology Filter Metric Set

open scoped NNReal Topology

variable {α β : Type*} [PseudoMetricSpace α]

open Finset

variable {X : β → Type*} [Fintype β] [∀ b, PseudoMetricSpace (X b)]

-- INSTANCE (free from Core): pseudoMetricSpacePi

lemma nndist_pi_le_iff {f g : ∀ b, X b} {r : ℝ≥0} :
    nndist f g ≤ r ↔ ∀ b, nndist (f b) (g b) ≤ r := by simp [nndist_pi_def]

lemma nndist_pi_lt_iff {f g : ∀ b, X b} {r : ℝ≥0} (hr : 0 < r) :
    nndist f g < r ↔ ∀ b, nndist (f b) (g b) < r := by
  simp [nndist_pi_def, Finset.sup_lt_iff hr]

lemma nndist_pi_eq_iff {f g : ∀ b, X b} {r : ℝ≥0} (hr : 0 < r) :
    nndist f g = r ↔ (∃ i, nndist (f i) (g i) = r) ∧ ∀ b, nndist (f b) (g b) ≤ r := by
  rw [eq_iff_le_not_lt, nndist_pi_lt_iff hr, nndist_pi_le_iff, not_forall, and_comm]
  simp_rw [not_lt, and_congr_left_iff, le_antisymm_iff]
  intro h
  refine exists_congr fun b => ?_
  apply (and_iff_right <| h _).symm

lemma dist_pi_lt_iff {f g : ∀ b, X b} {r : ℝ} (hr : 0 < r) :
    dist f g < r ↔ ∀ b, dist (f b) (g b) < r := by
  lift r to ℝ≥0 using hr.le
  exact nndist_pi_lt_iff hr

lemma dist_pi_le_iff {f g : ∀ b, X b} {r : ℝ} (hr : 0 ≤ r) :
    dist f g ≤ r ↔ ∀ b, dist (f b) (g b) ≤ r := by
  lift r to ℝ≥0 using hr
  exact nndist_pi_le_iff

lemma dist_pi_eq_iff {f g : ∀ b, X b} {r : ℝ} (hr : 0 < r) :
    dist f g = r ↔ (∃ i, dist (f i) (g i) = r) ∧ ∀ b, dist (f b) (g b) ≤ r := by
  lift r to ℝ≥0 using hr.le
  simp_rw [← coe_nndist, NNReal.coe_inj, nndist_pi_eq_iff hr, NNReal.coe_le_coe]

lemma dist_pi_le_iff' [Nonempty β] {f g : ∀ b, X b} {r : ℝ} :
    dist f g ≤ r ↔ ∀ b, dist (f b) (g b) ≤ r := by
  by_cases hr : 0 ≤ r
  · exact dist_pi_le_iff hr
  · exact iff_of_false (fun h => hr <| dist_nonneg.trans h) fun h =>
      hr <| dist_nonneg.trans <| h <| Classical.arbitrary _

lemma dist_pi_const_le (a b : α) : (dist (fun _ : β => a) fun _ => b) ≤ dist a b :=
  (dist_pi_le_iff dist_nonneg).2 fun _ => le_rfl

lemma nndist_pi_const_le (a b : α) : (nndist (fun _ : β => a) fun _ => b) ≤ nndist a b :=
  nndist_pi_le_iff.2 fun _ => le_rfl
