/-
Extracted from Topology/Instances/Real/Lemmas.lean
Genuine: 18 of 21 | Dissolved: 3 | Infrastructure: 0
-/
import Origin.Core

/-!
# Topological properties of ℝ
-/

assert_not_exists UniformOnFun

noncomputable section

open Filter Int Metric Set TopologicalSpace Bornology

open scoped Topology Uniformity Interval

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

theorem Real.isTopologicalBasis_Ioo_rat :
    @IsTopologicalBasis ℝ _ (⋃ (a : ℚ) (b : ℚ) (_ : a < b), {Ioo (a : ℝ) b}) :=
  isTopologicalBasis_of_isOpen_of_nhds (by simp +contextual [isOpen_Ioo])
    fun a _ hav hv =>
    let ⟨_, _, ⟨hl, hu⟩, h⟩ := mem_nhds_iff_exists_Ioo_subset.mp (IsOpen.mem_nhds hv hav)
    let ⟨q, hlq, hqa⟩ := exists_rat_btwn hl
    let ⟨p, hap, hpu⟩ := exists_rat_btwn hu
    ⟨Ioo q p, by
      simp only [mem_iUnion]
      exact ⟨q, p, Rat.cast_lt.1 <| hqa.trans hap, rfl⟩, ⟨hqa, hap⟩, fun _ ⟨hqa', ha'p⟩ =>
      h ⟨hlq.trans hqa', ha'p.trans hpu⟩⟩

#adaptation_note /-- After https://github.com/leanprover/lean4/pull/12179

the simpNF linter complains about this being `@[simp]`. -/

theorem Real.cobounded_eq : cobounded ℝ = atBot ⊔ atTop := by
  simp only [← comap_dist_right_atTop (0 : ℝ), Real.dist_eq, sub_zero, comap_abs_atTop]

theorem Real.mem_closure_iff {s : Set ℝ} {x : ℝ} :
    x ∈ closure s ↔ ∀ ε > 0, ∃ y ∈ s, |y - x| < ε := by
  simp [mem_closure_iff_nhds_basis nhds_basis_ball, Real.dist_eq]

theorem Real.uniformContinuous_inv (s : Set ℝ) {r : ℝ} (r0 : 0 < r) (H : ∀ x ∈ s, r ≤ |x|) :
    UniformContinuous fun p : s => p.1⁻¹ :=
  Metric.uniformContinuous_iff.2 fun _ε ε0 =>
    let ⟨δ, δ0, Hδ⟩ := rat_inv_continuous_lemma abs ε0 r0
    ⟨δ, δ0, fun {a b} h => Hδ (H _ a.2) (H _ b.2) h⟩

theorem Real.uniformContinuous_abs : UniformContinuous (abs : ℝ → ℝ) :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨ε, ε0, fun _ _ ↦ lt_of_le_of_lt (abs_abs_sub_abs_le_abs_sub _ _)⟩

-- DISSOLVED: Real.continuous_inv

theorem Real.uniformContinuous_mul (s : Set (ℝ × ℝ)) {r₁ r₂ : ℝ}
    (H : ∀ x ∈ s, |(x : ℝ × ℝ).1| < r₁ ∧ |x.2| < r₂) :
    UniformContinuous fun p : s => p.1.1 * p.1.2 :=
  Metric.uniformContinuous_iff.2 fun _ε ε0 =>
    let ⟨δ, δ0, Hδ⟩ := rat_mul_continuous_lemma abs ε0
    ⟨δ, δ0, fun {a b} h =>
      let ⟨h₁, h₂⟩ := max_lt_iff.1 h
      Hδ (H _ a.2).1 (H _ b.2).2 h₁ h₂⟩

theorem Real.totallyBounded_ball (x ε : ℝ) : TotallyBounded (ball x ε) := by
  rw [Real.ball_eq_Ioo]; apply totallyBounded_Ioo

theorem Real.subfield_eq_of_closed {K : Subfield ℝ} (hc : IsClosed (K : Set ℝ)) : K = ⊤ := by
  rw [SetLike.ext'_iff, Subfield.coe_top, ← hc.closure_eq]
  refine Rat.denseRange_cast.mono ?_ |>.closure_eq
  rintro - ⟨_, rfl⟩
  exact SubfieldClass.ratCast_mem K _

theorem Real.exists_seq_rat_strictMono_tendsto (x : ℝ) :
    ∃ u : ℕ → ℚ, StrictMono u ∧ (∀ n, u n < x) ∧ Tendsto (u · : ℕ → ℝ) atTop (𝓝 x) :=
  Rat.denseRange_cast.exists_seq_strictMono_tendsto Rat.cast_strictMono.monotone x

theorem Real.exists_seq_rat_strictAnti_tendsto (x : ℝ) :
    ∃ u : ℕ → ℚ, StrictAnti u ∧ (∀ n, x < u n) ∧ Tendsto (u · : ℕ → ℝ) atTop (𝓝 x) :=
  Rat.denseRange_cast.exists_seq_strictAnti_tendsto Rat.cast_strictMono.monotone x

theorem closure_ordConnected_inter_rat {s : Set ℝ} (conn : s.OrdConnected) (nt : s.Nontrivial) :
    closure (s ∩ .range Rat.cast) = closure s :=
  (closure_mono inter_subset_left).antisymm <| isClosed_closure.closure_subset_iff.mpr fun x hx ↦
    Real.mem_closure_iff.mpr fun ε ε_pos ↦ by
      have ⟨z, hz, ne⟩ := nt.exists_ne x
      refine ne.lt_or_gt.elim (fun lt ↦ ?_) fun lt ↦ ?_
      · have ⟨q, h₁, h₂⟩ := exists_rat_btwn (max_lt lt (sub_lt_self x ε_pos))
        rw [max_lt_iff] at h₁
        refine ⟨q, ⟨conn.out hz hx ⟨h₁.1.le, h₂.le⟩, q, rfl⟩, ?_⟩
        simpa only [abs_sub_comm, abs_of_pos (sub_pos.mpr h₂), sub_lt_comm] using h₁.2
      · have ⟨q, h₁, h₂⟩ := exists_rat_btwn (lt_min lt (lt_add_of_pos_right x ε_pos))
        rw [lt_min_iff] at h₂
        refine ⟨q, ⟨conn.out hx hz ⟨h₁.le, h₂.1.le⟩, q, rfl⟩, ?_⟩
        simpa only [abs_of_pos (sub_pos.2 h₁), sub_lt_iff_lt_add'] using h₂.2

theorem closure_of_rat_image_lt {q : ℚ} :
    closure (((↑) : ℚ → ℝ) '' { x | q < x }) = { r | ↑q ≤ r } := by
  convert closure_ordConnected_inter_rat (ordConnected_Ioi (a := (q : ℝ))) _ using 1
  · congr!; aesop
  · exact (closure_Ioi _).symm
  · exact ⟨q + 1, show (q : ℝ) < _ by linarith, q + 2, show (q : ℝ) < _ by linarith, by simp⟩

end

section Periodic

namespace Function

-- DISSOLVED: Periodic.compact_of_continuous

-- DISSOLVED: Periodic.isBounded_of_continuous

end Function

end Periodic

section Monotone

variable {ι : Type*} [Preorder ι] [Nonempty ι]

theorem Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici {f : ℕ → ℝ} {k : ℕ}
    (h_mon : MonotoneOn f (Ici k)) (h_bdd : BddAbove (f '' Ici k)) :
    Tendsto f atTop (𝓝 (sSup (f '' Ici k))) := by
  rw [← range_add_eq_image_Ici] at h_bdd
  rw [Ici, ← monotone_add_nat_iff_monotoneOn_nat_Ici] at h_mon
  rw [← tendsto_add_atTop_iff_nat k, ← range_add_eq_image_Ici, sSup_range]
  exact tendsto_atTop_ciSup h_mon h_bdd

theorem Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici {f : ℕ → ℝ} {k : ℕ}
    (h_ant : AntitoneOn f (Ici k)) (h_bdd : BddBelow (f '' Ici k)) :
    Tendsto f atTop (𝓝 (sInf (f '' Ici k))) := by
  rw [← range_add_eq_image_Ici] at h_bdd
  rw [Ici, ← antitone_add_nat_iff_antitoneOn_nat_Ici] at h_ant
  rw [← tendsto_add_atTop_iff_nat k, ← range_add_eq_image_Ici, sInf_range]
  exact tendsto_atTop_ciInf h_ant h_bdd

variable [IsDirected ι (· ≤ ·)]

theorem Real.isLUB_of_tendsto_monotone_bddAbove {f : ι → ℝ}
    {x : ℝ} (h_tto : Tendsto f atTop (𝓝 x))
    (h_mon : Monotone f) (h_bdd : BddAbove (range f)) : IsLUB (range f) x := by
  rw [tendsto_nhds_unique h_tto (tendsto_atTop_ciSup h_mon h_bdd)]
  exact isLUB_ciSup h_bdd

theorem Real.isGLB_of_tendsto_antitone_bddBelow {f : ι → ℝ}
    {x : ℝ} (h_tto : Tendsto f atTop (𝓝 x))
    (h_ant : Antitone f) (h_bdd : BddBelow (range f)) : IsGLB (range f) x := by
  rw [tendsto_nhds_unique h_tto (tendsto_atTop_ciInf h_ant h_bdd)]
  exact isGLB_ciInf h_bdd

theorem Real.isLUB_of_tendsto_monotoneOn_bddAbove_nat_Ici {f : ℕ → ℝ} {k : ℕ}
    {x : ℝ} (h_tto : Tendsto f atTop (𝓝 x))
    (h_mon : MonotoneOn f (Ici k)) (h_bdd : BddAbove (f '' Ici k)) : IsLUB (f '' Ici k) x := by
  rw [tendsto_nhds_unique h_tto
    (Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici h_mon h_bdd)]
  exact isLUB_csSup (image_nonempty.mpr nonempty_Ici) h_bdd

theorem Real.isGLB_of_tendsto_antitoneOn_bddBelow_nat_Ici {f : ℕ → ℝ} {k : ℕ}
    {x : ℝ} (h_tto : Tendsto f atTop (𝓝 x))
    (h_ant : AntitoneOn f (Ici k)) (h_bdd : BddBelow (f '' Ici k)) : IsGLB (f '' Ici k) x := by
  rw [tendsto_nhds_unique h_tto
    (Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici h_ant h_bdd)]
  exact isGLB_csInf (image_nonempty.mpr nonempty_Ici) h_bdd

end Monotone
