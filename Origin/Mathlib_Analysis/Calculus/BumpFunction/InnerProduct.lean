/-
Extracted from Analysis/Calculus/BumpFunction/InnerProduct.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Smooth bump functions in inner product spaces

In this file we prove that a real inner product space has smooth bump functions,
see `hasContDiffBump_of_innerProductSpace`.

## Keywords

smooth function, bump function, inner product space
-/

open Function Real

open scoped Topology

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def ContDiffBumpBase.ofInnerProductSpace : ContDiffBumpBase E where
  toFun R x := smoothTransition ((R - ‖x‖) / (R - 1))
  mem_Icc _ _ := ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
  symmetric _ _ := by simp only [norm_neg]
  smooth := by
    rintro ⟨R, x⟩ ⟨hR : 1 < R, -⟩
    apply ContDiffAt.contDiffWithinAt
    rw [← sub_pos] at hR
    rcases eq_or_ne x 0 with rfl | hx
    · have A : ContinuousAt (fun p : ℝ × E ↦ (p.1 - ‖p.2‖) / (p.1 - 1)) (R, 0) := by
        fun_prop (disch := positivity)
      have B : ∀ᶠ p in 𝓝 (R, (0 : E)), 1 ≤ (p.1 - ‖p.2‖) / (p.1 - 1) :=
        A.eventually <| le_mem_nhds <| (one_lt_div hR).2 <| sub_lt_sub_left (by simp) _
      refine (contDiffAt_const (c := 1)).congr_of_eventuallyEq <| B.mono fun _ ↦
        smoothTransition.one_of_one_le
    · refine smoothTransition.contDiffAt.comp _ (ContDiffAt.div ?_ (by fun_prop) hR.ne')
      exact contDiffAt_fst.sub (contDiffAt_snd.norm ℝ hx)
  eq_one _ hR _ hx := smoothTransition.one_of_one_le <| (one_le_div <| sub_pos.2 hR).2 <|
    sub_le_sub_left hx _
  support R hR := by
    ext x
    rw [mem_support, Ne, smoothTransition.zero_iff_nonpos, not_le, mem_ball_zero_iff]
    simp [hR]

-- INSTANCE (free from Core): (priority
