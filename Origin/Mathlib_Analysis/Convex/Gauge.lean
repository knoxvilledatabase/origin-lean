/-
Extracted from Analysis/Convex/Gauge.lean
Genuine: 6 of 7 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The Minkowski functional

This file defines the Minkowski functional, aka gauge.

The Minkowski functional of a set `s` is the function which associates each point to how much you
need to scale `s` for `x` to be inside it. When `s` is symmetric, convex and absorbent, its gauge is
a seminorm. Reciprocally, any seminorm arises as the gauge of some set, namely its unit ball. This
induces the equivalence of seminorms and locally convex topological vector spaces.

## Main declarations

For a real vector space,
* `gauge`: Aka Minkowski functional. `gauge s x` is the least (actually, an infimum) `r` such
  that `x ∈ r • s`.
* `gaugeSeminorm`: The Minkowski functional as a seminorm, when `s` is symmetric, convex and
  absorbent.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

Minkowski functional, gauge
-/

open NormedField Set

open scoped Pointwise Topology NNReal

noncomputable section

variable {𝕜 E : Type*}

section AddCommGroup

variable [AddCommGroup E] [Module ℝ E]

def gauge (s : Set E) (x : E) : ℝ :=
  sInf { r : ℝ | 0 < r ∧ x ∈ r • s }

variable {s t : Set E} {x : E} {a : ℝ}

theorem gauge_def' : gauge s x = sInf {r ∈ Set.Ioi (0 : ℝ) | r⁻¹ • x ∈ s} := by
  congrm sInf {r | ?_}
  exact and_congr_right fun hr => mem_smul_set_iff_inv_smul_mem₀ hr.ne' _ _

private theorem gauge_set_bddBelow : BddBelow { r : ℝ | 0 < r ∧ x ∈ r • s } :=
  ⟨0, fun _ hr => hr.1.le⟩

theorem Absorbent.gauge_set_nonempty (absorbs : Absorbent ℝ s) :
    { r : ℝ | 0 < r ∧ x ∈ r • s }.Nonempty :=
  let ⟨r, hr₁, hr₂⟩ := (absorbs x).exists_pos
  ⟨r, hr₁, hr₂ r (Real.norm_of_nonneg hr₁.le).ge rfl⟩

theorem gauge_mono (hs : Absorbent ℝ s) (h : s ⊆ t) : gauge t ≤ gauge s := fun _ => by
  unfold gauge
  gcongr; exacts [gauge_set_bddBelow, hs.gauge_set_nonempty]

theorem exists_lt_of_gauge_lt (absorbs : Absorbent ℝ s) (h : gauge s x < a) :
    ∃ b, 0 < b ∧ b < a ∧ x ∈ b • s := by
  obtain ⟨b, ⟨hb, hx⟩, hba⟩ := exists_lt_of_csInf_lt absorbs.gauge_set_nonempty h
  exact ⟨b, hb, hba, hx⟩
