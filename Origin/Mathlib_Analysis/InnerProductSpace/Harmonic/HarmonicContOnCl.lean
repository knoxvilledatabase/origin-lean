/-
Extracted from Analysis/InnerProductSpace/Harmonic/HarmonicContOnCl.lean
Genuine: 9 of 9 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Functions Harmonic on a Domain and Continuous on Its Closure

Many theorems in harmonic analysis assume that a function is harmonic on a domain and is continuous
on its closure. In this file we define a predicate `HarmonicContOnCl` that expresses this property
and prove basic facts about this predicate.
-/

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f f₁ f₂ : E → F}
  {x : E} {s : Set E} {c : ℝ}

open Laplacian Metric Topology

namespace InnerProductSpace

structure HarmonicContOnCl (f : E → F) (s : Set E) : Prop where
  protected harmonicOnNhd : HarmonicOnNhd f s
  protected continuousOn : ContinuousOn f (closure s)

theorem HarmonicOnNhd.harmonicContOnCl (h : HarmonicOnNhd f (closure s)) :
    HarmonicContOnCl f s :=
  ⟨h.mono subset_closure, h.continuousOn⟩

theorem IsClosed.harmonicContOnCl_iff (hs : IsClosed s) :
    HarmonicContOnCl f s ↔ HarmonicOnNhd f s where
  mp := (·.1 · ·)
  mpr h := by
    rw [← hs.closure_eq] at h
    exact h.harmonicContOnCl

theorem harmonicContOnCl_const {c : F} : HarmonicContOnCl (fun _ : E ↦ c) s :=
  ⟨harmonicOnNhd_const c, continuousOn_const⟩

namespace HarmonicContOnCl

theorem continuousOn_ball [NormedSpace ℝ E] {x : E} {r : ℝ} (h : HarmonicContOnCl f (ball x r)) :
    ContinuousOn f (closedBall x r) := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero]
    exact continuousOn_singleton f x
  · rw [← closure_ball x hr]
    exact h.continuousOn

theorem mk_ball {x : E} {r : ℝ} (hd : HarmonicOnNhd f (ball x r))
    (hc : ContinuousOn f (closedBall x r)) :
    HarmonicContOnCl f (ball x r) :=
  ⟨hd, hc.mono <| closure_ball_subset_closedBall⟩

theorem contDiffAt (h : HarmonicContOnCl f s) (hx : x ∈ s) :
    ContDiffAt ℝ 2 f x := (h.1 x hx).1

theorem differentiableAt (h : HarmonicContOnCl f s) (hx : x ∈ s) :
    DifferentiableAt ℝ f x := (h.contDiffAt hx).differentiableAt two_ne_zero

theorem mono {t : Set E} (h : HarmonicContOnCl f s) (ht : t ⊆ s) :
    HarmonicContOnCl f t := ⟨h.harmonicOnNhd.mono ht, h.continuousOn.mono (closure_mono ht)⟩
