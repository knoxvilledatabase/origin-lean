/-
Extracted from Analysis/Calculus/BumpFunction/FiniteDimension.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bump functions in finite-dimensional vector spaces

Let `E` be a finite-dimensional real normed vector space. We show that any open set `s` in `E` is
exactly the support of a smooth function taking values in `[0, 1]`,
in `IsOpen.exists_contDiff_support_eq`.

Then we use this construction to construct bump functions with nice behavior, by convolving
the indicator function of `closedBall 0 1` with a function as above with `s = ball 0 D`.
-/

noncomputable section

open Set Metric TopologicalSpace Function Asymptotics MeasureTheory Module

  ContinuousLinearMap Filter MeasureTheory.Measure Bornology

open scoped Pointwise Topology NNReal Convolution ContDiff

variable {E : Type*} [NormedAddCommGroup E]

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_contDiff_tsupport_subset {s : Set E} {x : E} {n : ℕ∞} (hs : s ∈ 𝓝 x) :
    ∃ f : E → ℝ,
      tsupport f ⊆ s ∧ HasCompactSupport f ∧ ContDiff ℝ n f ∧ range f ⊆ Icc 0 1 ∧ f x = 1 := by
  obtain ⟨d : ℝ, d_pos : 0 < d, hd : Euclidean.closedBall x d ⊆ s⟩ :=
    Euclidean.nhds_basis_closedBall.mem_iff.1 hs
  let c : ContDiffBump (toEuclidean x) :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos d_pos
      rIn_lt_rOut := half_lt_self d_pos }
  let f : E → ℝ := c ∘ toEuclidean
  have f_supp : f.support ⊆ Euclidean.ball x d := by
    intro y hy
    have : toEuclidean y ∈ Function.support c := by
      simpa only [Function.mem_support, Function.comp_apply, Ne] using hy
    rwa [c.support_eq] at this
  have f_tsupp : tsupport f ⊆ Euclidean.closedBall x d := by
    rw [tsupport, ← Euclidean.closure_ball _ d_pos.ne']
    exact closure_mono f_supp
  refine ⟨f, f_tsupp.trans hd, ?_, ?_, ?_, ?_⟩
  · refine isCompact_of_isClosed_isBounded isClosed_closure ?_
    have : IsBounded (Euclidean.closedBall x d) := Euclidean.isCompact_closedBall.isBounded
    refine this.subset (Euclidean.isClosed_closedBall.closure_subset_iff.2 ?_)
    exact f_supp.trans Euclidean.ball_subset_closedBall
  · apply c.contDiff.comp
    exact ContinuousLinearEquiv.contDiff _
  · rintro t ⟨y, rfl⟩
    exact ⟨c.nonneg, c.le_one⟩
  · apply c.one_of_mem_closedBall
    apply mem_closedBall_self
    exact (half_pos d_pos).le
