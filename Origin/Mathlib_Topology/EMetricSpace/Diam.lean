/-
Extracted from Topology/EMetricSpace/Diam.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Diameters of sets in extended metric spaces

In this file we define the diameter of a set in the extended metric space
as an extended nonnegative real number.
-/

open Set Filter

open scoped Uniformity Topology Filter NNReal ENNReal Pointwise

variable {α X : Type*} {s t : Set X} {x y z : X}

namespace Metric

section PseudoEMetricSpace

variable [PseudoEMetricSpace X]

noncomputable def ediam (s : Set X) :=
  ⨆ (x ∈ s) (y ∈ s), edist x y

theorem ediam_eq_sSup (s : Set X) : ediam s = sSup (image2 edist s s) := sSup_image2.symm

theorem ediam_le_iff {d : ℝ≥0∞} : ediam s ≤ d ↔ ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ d := by
  simp only [ediam, iSup_le_iff]

theorem ediam_image_le_iff {d : ℝ≥0∞} {f : α → X} {s : Set α} :
    ediam (f '' s) ≤ d ↔ ∀ x ∈ s, ∀ y ∈ s, edist (f x) (f y) ≤ d := by
  simp only [ediam_le_iff, forall_mem_image]

theorem edist_le_of_ediam_le {d} (hx : x ∈ s) (hy : y ∈ s) (hd : ediam s ≤ d) : edist x y ≤ d :=
  ediam_le_iff.1 hd x hx y hy

theorem edist_le_ediam_of_mem (hx : x ∈ s) (hy : y ∈ s) : edist x y ≤ ediam s :=
  edist_le_of_ediam_le hx hy le_rfl

theorem ediam_le {d : ℝ≥0∞} (h : ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ d) : ediam s ≤ d :=
  ediam_le_iff.2 h

theorem ediam_subsingleton (hs : s.Subsingleton) : ediam s = 0 :=
  nonpos_iff_eq_zero.1 <| ediam_le fun _x hx y hy => (hs hx hy).symm ▸ edist_self y ▸ le_rfl

alias _root_.Set.Subsingleton.ediam_eq := ediam_subsingleton
