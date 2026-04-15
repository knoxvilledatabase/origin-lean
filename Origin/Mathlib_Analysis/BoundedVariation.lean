/-
Extracted from Analysis/BoundedVariation.lean
Genuine: 6 of 9 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Almost everywhere differentiability of functions with locally bounded variation

In this file we show that a bounded variation function is differentiable almost everywhere.
This implies that Lipschitz functions from the real line into finite-dimensional vector space
are also differentiable almost everywhere.

## Main definitions and results

* `LocallyBoundedVariationOn.ae_differentiableWithinAt` shows that a bounded variation
  function on a subset of ℝ into a finite-dimensional real vector space is differentiable almost
  everywhere, with `DifferentiableWithinAt` in its conclusion.
* `BoundedVariationOn.ae_differentiableAt_of_mem_uIcc` shows that a bounded variation function on
  an interval of ℝ into a finite-dimensional real vector space is differentiable almost everywhere,
  with `DifferentiableAt` in its conclusion.
* `LipschitzOnWith.ae_differentiableWithinAt` is the same result for Lipschitz functions.

We also give several variations around these results.

-/

open scoped NNReal Topology

open Set MeasureTheory Filter

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

namespace LocallyBoundedVariationOn

theorem ae_differentiableWithinAt_of_mem_pi {ι : Type*} [Fintype ι] {f : ℝ → ι → ℝ} {s : Set ℝ}
    (h : LocallyBoundedVariationOn f s) : ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  have A : ∀ i : ι, LipschitzWith 1 fun x : ι → ℝ => x i := fun i => LipschitzWith.eval i
  have : ∀ i : ι, ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ (fun x : ℝ => f x i) s x := fun i ↦ by
    apply ae_differentiableWithinAt_of_mem_real
    exact LipschitzWith.comp_locallyBoundedVariationOn (A i) h
  filter_upwards [ae_all_iff.2 this] with x hx xs
  exact differentiableWithinAt_pi.2 fun i => hx i xs

theorem ae_differentiableWithinAt_of_mem {f : ℝ → V} {s : Set ℝ}
    (h : LocallyBoundedVariationOn f s) : ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  let A := (Module.Basis.ofVectorSpace ℝ V).equivFun.toContinuousLinearEquiv
  suffices H : ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ (A ∘ f) s x by
    filter_upwards [H] with x hx xs
    exact (ContinuousLinearEquiv.comp_differentiableWithinAt_iff _).mp (hx xs)
  apply ae_differentiableWithinAt_of_mem_pi
  exact A.lipschitz.comp_locallyBoundedVariationOn h

theorem _root_.BoundedVariationOn.ae_differentiableAt_of_mem_uIcc {f : ℝ → V} {a b : ℝ}
    (h : BoundedVariationOn f (uIcc a b)) : ∀ᵐ x, x ∈ uIcc a b → DifferentiableAt ℝ f x := by
  have h₁ : ∀ᵐ x, x ≠ min a b := by simp [ae_iff, measure_singleton]
  have h₂ : ∀ᵐ x, x ≠ max a b := by simp [ae_iff, measure_singleton]
  filter_upwards [h.locallyBoundedVariationOn.ae_differentiableWithinAt_of_mem, h₁, h₂]
    with x hx₁ hx₂ hx₃ hx₄
  rw [uIcc, mem_Icc] at hx₄
  exact (hx₁ hx₄).differentiableAt
    (Icc_mem_nhds (lt_of_le_of_ne hx₄.left hx₂.symm) (lt_of_le_of_ne hx₄.right hx₃))

theorem ae_differentiableWithinAt {f : ℝ → V} {s : Set ℝ} (h : LocallyBoundedVariationOn f s)
    (hs : MeasurableSet s) : ∀ᵐ x ∂volume.restrict s, DifferentiableWithinAt ℝ f s x := by
  rw [ae_restrict_iff' hs]
  exact h.ae_differentiableWithinAt_of_mem

theorem ae_differentiableAt {f : ℝ → V} (h : LocallyBoundedVariationOn f univ) :
    ∀ᵐ x, DifferentiableAt ℝ f x := by
  filter_upwards [h.ae_differentiableWithinAt_of_mem] with x hx
  rw [differentiableWithinAt_univ] at hx
  exact hx (mem_univ _)

end LocallyBoundedVariationOn

theorem LipschitzWith.ae_differentiableAt_real {C : ℝ≥0} {f : ℝ → V} (h : LipschitzWith C f) :
    ∀ᵐ x, DifferentiableAt ℝ f x :=
  (h.locallyBoundedVariationOn univ).ae_differentiableAt
