/-
Extracted from Topology/MetricSpace/Infsep.lean
Genuine: 16 of 16 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Infimum separation

This file defines the extended infimum separation of a set. This is approximately dual to the
diameter of a set, but where the extended diameter of a set is the supremum of the extended distance
between elements of the set, the extended infimum separation is the infimum of the (extended)
distance between *distinct* elements in the set.

We also define the infimum separation as the cast of the extended infimum separation to the reals.
This is the infimum of the distance between distinct elements of the set when in a pseudometric
space.

All lemmas and definitions are in the `Set` namespace to give access to dot notation.

## Main definitions
* `Set.einfsep`: Extended infimum separation of a set.
* `Set.infsep`: Infimum separation of a set (when in a pseudometric space).

-/

variable {α β : Type*}

namespace Set

section Einfsep

open ENNReal

open Function

noncomputable def einfsep [EDist α] (s : Set α) : ℝ≥0∞ :=
  ⨅ (x ∈ s) (y ∈ s) (_ : x ≠ y), edist x y

section EDist

variable [EDist α] {x y : α} {s t : Set α}

theorem le_einfsep_iff {d} :
    d ≤ s.einfsep ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ edist x y := by
  simp_rw [einfsep, le_iInf_iff]

theorem einfsep_zero : s.einfsep = 0 ↔ ∀ C > 0, ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ edist x y < C := by
  simp_rw [einfsep, ← _root_.bot_eq_zero, iInf_eq_bot, iInf_lt_iff, exists_prop]

theorem einfsep_pos : 0 < s.einfsep ↔ ∃ C > 0, ∀ x ∈ s, ∀ y ∈ s, x ≠ y → C ≤ edist x y := by
  rw [pos_iff_ne_zero, Ne, einfsep_zero]
  simp only [not_forall, not_exists, not_lt, exists_prop, not_and]

theorem einfsep_top :
    s.einfsep = ∞ ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → edist x y = ∞ := by
  simp_rw [einfsep, iInf_eq_top]

theorem einfsep_lt_top :
    s.einfsep < ∞ ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ edist x y < ∞ := by
  simp_rw [einfsep, iInf_lt_iff, exists_prop]

theorem einfsep_ne_top :
    s.einfsep ≠ ∞ ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ edist x y ≠ ∞ := by
  simp_rw [← lt_top_iff_ne_top, einfsep_lt_top]

theorem einfsep_lt_iff {d} :
    s.einfsep < d ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ edist x y < d := by
  simp_rw [einfsep, iInf_lt_iff, exists_prop]

theorem nontrivial_of_einfsep_lt_top (hs : s.einfsep < ∞) : s.Nontrivial := by
  rcases einfsep_lt_top.1 hs with ⟨_, hx, _, hy, hxy, _⟩
  exact ⟨_, hx, _, hy, hxy⟩

theorem nontrivial_of_einfsep_ne_top (hs : s.einfsep ≠ ∞) : s.Nontrivial :=
  nontrivial_of_einfsep_lt_top (lt_top_iff_ne_top.mpr hs)

theorem Subsingleton.einfsep (hs : s.Subsingleton) : s.einfsep = ∞ := by
  rw [einfsep_top]
  exact fun _ hx _ hy hxy => (hxy <| hs hx hy).elim

theorem le_einfsep_image_iff {d} {f : β → α} {s : Set β} : d ≤ einfsep (f '' s)
    ↔ ∀ x ∈ s, ∀ y ∈ s, f x ≠ f y → d ≤ edist (f x) (f y) := by
  simp_rw [le_einfsep_iff, forall_mem_image]

theorem le_edist_of_le_einfsep {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hd : d ≤ s.einfsep) : d ≤ edist x y :=
  le_einfsep_iff.1 hd x hx y hy hxy

theorem einfsep_le_edist_of_mem {x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y) :
    s.einfsep ≤ edist x y :=
  le_edist_of_le_einfsep hx hy hxy le_rfl

theorem einfsep_le_of_mem_of_edist_le {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hxy' : edist x y ≤ d) : s.einfsep ≤ d :=
  le_trans (einfsep_le_edist_of_mem hx hy hxy) hxy'

theorem le_einfsep {d} (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ edist x y) : d ≤ s.einfsep :=
  le_einfsep_iff.2 h
