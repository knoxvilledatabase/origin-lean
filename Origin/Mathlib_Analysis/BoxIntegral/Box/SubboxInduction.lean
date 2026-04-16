/-
Extracted from Analysis/BoxIntegral/Box/SubboxInduction.lean
Genuine: 9 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Analysis.BoxIntegral.Box.Basic
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

/-!
# Induction on subboxes

In this file we prove the following induction principle for `BoxIntegral.Box`, see
`BoxIntegral.Box.subbox_induction_on`. Let `p` be a predicate on `BoxIntegral.Box ι`, let `I` be a
box. Suppose that the following two properties hold true.

* Consider a smaller box `J ≤ I`. The hyperplanes passing through the center of `J` split it into
  `2 ^ n` boxes. If `p` holds true on each of these boxes, then it is true on `J`.
* For each `z` in the closed box `I.Icc` there exists a neighborhood `U` of `z` within `I.Icc` such
  that for every box `J ≤ I` such that `z ∈ J.Icc ⊆ U`, if `J` is homothetic to `I` with a
  coefficient of the form `1 / 2 ^ m`, then `p` is true on `J`.

Then `p I` is true.

## Tags

rectangular box, induction
-/

open Set Function Filter Topology

noncomputable section

namespace BoxIntegral

namespace Box

variable {ι : Type*} {I J : Box ι}

open Classical in

def splitCenterBox (I : Box ι) (s : Set ι) : Box ι where
  lower := s.piecewise (fun i ↦ (I.lower i + I.upper i) / 2) I.lower
  upper := s.piecewise I.upper fun i ↦ (I.lower i + I.upper i) / 2
  lower_lt_upper i := by
    dsimp only [Set.piecewise]
    split_ifs <;> simp only [left_lt_add_div_two, add_div_two_lt_right, I.lower_lt_upper]

theorem mem_splitCenterBox {s : Set ι} {y : ι → ℝ} :
    y ∈ I.splitCenterBox s ↔ y ∈ I ∧ ∀ i, (I.lower i + I.upper i) / 2 < y i ↔ i ∈ s := by
  simp only [splitCenterBox, mem_def, ← forall_and]
  refine forall_congr' fun i ↦ ?_
  dsimp only [Set.piecewise]
  split_ifs with hs <;> simp only [hs, iff_true, iff_false, not_lt]
  exacts [⟨fun H ↦ ⟨⟨(left_lt_add_div_two.2 (I.lower_lt_upper i)).trans H.1, H.2⟩, H.1⟩,
      fun H ↦ ⟨H.2, H.1.2⟩⟩,
    ⟨fun H ↦ ⟨⟨H.1, H.2.trans (add_div_two_lt_right.2 (I.lower_lt_upper i)).le⟩, H.2⟩,
      fun H ↦ ⟨H.1.1, H.2⟩⟩]

theorem splitCenterBox_le (I : Box ι) (s : Set ι) : I.splitCenterBox s ≤ I :=
  fun _ hx ↦ (mem_splitCenterBox.1 hx).1

theorem disjoint_splitCenterBox (I : Box ι) {s t : Set ι} (h : s ≠ t) :
    Disjoint (I.splitCenterBox s : Set (ι → ℝ)) (I.splitCenterBox t) := by
  rw [disjoint_iff_inf_le]
  rintro y ⟨hs, ht⟩; apply h
  ext i
  rw [mem_coe, mem_splitCenterBox] at hs ht
  rw [← hs.2, ← ht.2]

theorem injective_splitCenterBox (I : Box ι) : Injective I.splitCenterBox := fun _ _ H ↦
  by_contra fun Hne ↦ (I.disjoint_splitCenterBox Hne).ne (nonempty_coe _).ne_empty (H ▸ rfl)

@[simp]
theorem exists_mem_splitCenterBox {I : Box ι} {x : ι → ℝ} : (∃ s, x ∈ I.splitCenterBox s) ↔ x ∈ I :=
  ⟨fun ⟨s, hs⟩ ↦ I.splitCenterBox_le s hs, fun hx ↦
    ⟨{ i | (I.lower i + I.upper i) / 2 < x i }, mem_splitCenterBox.2 ⟨hx, fun _ ↦ Iff.rfl⟩⟩⟩

@[simps]
def splitCenterBoxEmb (I : Box ι) : Set ι ↪ Box ι :=
  ⟨splitCenterBox I, injective_splitCenterBox I⟩

@[simp]
theorem iUnion_coe_splitCenterBox (I : Box ι) : ⋃ s, (I.splitCenterBox s : Set (ι → ℝ)) = I := by
  ext x
  simp

@[simp]
theorem upper_sub_lower_splitCenterBox (I : Box ι) (s : Set ι) (i : ι) :
    (I.splitCenterBox s).upper i - (I.splitCenterBox s).lower i = (I.upper i - I.lower i) / 2 := by
  by_cases i ∈ s <;> field_simp [splitCenterBox] <;> field_simp [mul_two, two_mul]

end Box

end BoxIntegral
