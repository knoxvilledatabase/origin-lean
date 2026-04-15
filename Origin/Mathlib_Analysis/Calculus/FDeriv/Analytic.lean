/-
Extracted from Analysis/Calculus/FDeriv/Analytic.lean
Genuine: 3 of 7 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Fréchet derivatives of analytic functions.

A function expressible as a power series at a point has a Fréchet derivative there.
Also the special case in terms of `deriv` when the domain is 1-dimensional.

As an application, we show that continuous multilinear maps are smooth. We also compute their
iterated derivatives, in `ContinuousMultilinearMap.iteratedFDeriv_eq`.

## Main definitions and results

* `AnalyticAt.differentiableAt` : an analytic function at a point is differentiable there.
* `AnalyticOnNhd.fderiv` : in a complete space, if a function is analytic on a
  neighborhood of a set `s`, so is its derivative.
* `AnalyticOnNhd.fderiv_of_isOpen` : if a function is analytic on a neighborhood of an
  open set `s`, so is its derivative.
* `AnalyticOn.fderivWithin` : if a function is analytic on a set of unique differentiability,
  so is its derivative within this set.
* `OpenPartialHomeomorph.analyticAt_symm` : if an open partial homeomorphism `f` is analytic at a
  point `f.symm a`, with invertible derivative, then its inverse is analytic at `a`.

## Comments on completeness

Some theorems need a complete space, some don't, for the following reason.

(1) If a function is analytic at a point `x`, then it is differentiable there (with derivative given
by the first term in the power series). There is no issue of convergence here.

(2) If a function has a power series on a ball `B (x, r)`, there is no guarantee that the power
series for the derivative will converge at `y ≠ x`, if the space is not complete. So, to deduce
that `f` is differentiable at `y`, one needs completeness in general.

(3) However, if a function `f` has a power series on a ball `B (x, r)`, and is a priori known to be
differentiable at some point `y ≠ x`, then the power series for the derivative of `f` will
automatically converge at `y`, towards the given derivative: this follows from the facts that this
is true in the completion (thanks to the previous point) and that the map to the completion is
an embedding.

(4) Therefore, if one assumes `AnalyticOn 𝕜 f s` where `s` is an open set, then `f` is analytic
therefore differentiable at every point of `s`, by (1), so by (3) the power series for its
derivative converges on whole balls. Therefore, the derivative of `f` is also analytic on `s`. The
same holds if `s` is merely a set with unique differentials.

(5) However, this does not work for `AnalyticOnNhd 𝕜 f s`, as we don't get for free
differentiability at points in a neighborhood of `s`. Therefore, the theorem that deduces
`AnalyticOnNhd 𝕜 (fderiv 𝕜 f) s` from `AnalyticOnNhd 𝕜 f s` requires completeness of the space.

-/

open Filter Asymptotics Set

open scoped ENNReal Topology

universe u v

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section fderiv

variable {p : FormalMultilinearSeries 𝕜 E F} {r : ℝ≥0∞}

variable {f : E → F} {x : E} {s : Set E}

theorem HasFPowerSeriesWithinAt.hasStrictFDerivWithinAt (h : HasFPowerSeriesWithinAt f p s x) :
    (fun y ↦ f y.1 - f y.2 - (continuousMultilinearCurryFin1 𝕜 E F (p 1)) (y.1 - y.2))
      =o[𝓝[insert x s ×ˢ insert x s] (x, x)] fun y ↦ y.1 - y.2 := by
  refine h.isBigO_image_sub_norm_mul_norm_sub.trans_isLittleO (IsLittleO.of_norm_right ?_)
  refine isLittleO_iff_exists_eq_mul.2 ⟨fun y => ‖y - (x, x)‖, ?_, EventuallyEq.rfl⟩
  apply Tendsto.mono_left _ nhdsWithin_le_nhds
  refine (continuous_id.sub continuous_const).norm.tendsto' _ _ ?_
  rw [_root_.id, sub_self, norm_zero]

theorem HasFPowerSeriesAt.hasStrictFDerivAt (h : HasFPowerSeriesAt f p x) :
    HasStrictFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) x := by
  simpa only [hasStrictFDerivAt_iff_isLittleO, Set.insert_eq_of_mem, Set.mem_univ,
      Set.univ_prod_univ, nhdsWithin_univ]
    using (h.hasFPowerSeriesWithinAt (s := Set.univ)).hasStrictFDerivWithinAt

theorem HasFPowerSeriesWithinAt.hasFDerivWithinAt (h : HasFPowerSeriesWithinAt f p s x) :
    HasFDerivWithinAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) (insert x s) x := by
  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  have : Tendsto (fun y ↦ (y, x)) (𝓝[insert x s] x) (𝓝[insert x s ×ˢ insert x s] (x, x)) := by
    rw [nhdsWithin_prod_eq]
    exact Tendsto.prodMk tendsto_id (tendsto_const_nhdsWithin (by simp))
  exact this (isLittleO_iff.1 h.hasStrictFDerivWithinAt hc)
