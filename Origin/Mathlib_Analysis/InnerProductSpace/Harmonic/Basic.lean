/-
Extracted from Analysis/InnerProductSpace/Harmonic/Basic.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Harmonic Functions

This file defines harmonic functions on real, finite-dimensional, inner product spaces `E`.
-/

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {f f₁ f₂ : E → F}
  {x : E} {s t : Set E} {c : ℝ}

open Topology Laplacian

namespace InnerProductSpace

/-!
## Definition
-/

variable (f x) in

def HarmonicAt := (ContDiffAt ℝ 2 f x) ∧ (Δ f =ᶠ[𝓝 x] 0)

variable (f s) in

def HarmonicOnNhd := ∀ x ∈ s, HarmonicAt f x

lemma HarmonicOnNhd.contDiffOn (hf : HarmonicOnNhd f s) : ContDiffOn ℝ 2 f s :=
  fun x hx ↦ (hf x hx).1.contDiffWithinAt

/-!
## Elementary Properties
-/

theorem harmonicAt_congr_nhds {f₁ f₂ : E → F} {x : E} (h : f₁ =ᶠ[𝓝 x] f₂) :
    HarmonicAt f₁ x ↔ HarmonicAt f₂ x := by
  constructor <;> intro hf
  · exact ⟨hf.1.congr_of_eventuallyEq h.symm, (laplacian_congr_nhds h.symm).trans hf.2⟩
  · exact ⟨hf.1.congr_of_eventuallyEq h, (laplacian_congr_nhds h).trans hf.2⟩

theorem HarmonicAt.eventually {f : E → F} {x : E} (h : HarmonicAt f x) :
    ∀ᶠ y in 𝓝 x, HarmonicAt f y := by
  filter_upwards [h.1.eventually (by simp), h.2.eventually_nhds] with a h₁a h₂a
  exact ⟨h₁a, h₂a⟩
