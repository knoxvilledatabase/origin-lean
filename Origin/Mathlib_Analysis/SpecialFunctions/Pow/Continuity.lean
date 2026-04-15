/-
Extracted from Analysis/SpecialFunctions/Pow/Continuity.lean
Genuine: 8 of 18 | Dissolved: 10 | Infrastructure: 0
-/
import Origin.Core

/-!
# Continuity of power functions

This file contains lemmas about continuity of the power functions on `ℂ`, `ℝ`, `ℝ≥0`, and `ℝ≥0∞`.
-/

noncomputable section

open Real Topology NNReal ENNReal Filter ComplexConjugate Finset Set

section CpowLimits

/-!
## Continuity for complex powers
-/

open Complex

variable {α : Type*}

-- DISSOLVED: zero_cpow_eq_nhds

-- DISSOLVED: cpow_eq_nhds

-- DISSOLVED: cpow_eq_nhds'

-- DISSOLVED: continuousAt_const_cpow

-- DISSOLVED: continuousAt_const_cpow'

theorem continuousAt_cpow {p : ℂ × ℂ} (hp_fst : p.fst ∈ slitPlane) :
    ContinuousAt (fun x : ℂ × ℂ => x.1 ^ x.2) p := by
  rw [continuousAt_congr (cpow_eq_nhds' <| slitPlane_ne_zero hp_fst)]
  refine continuous_exp.continuousAt.comp ?_
  exact
    ContinuousAt.mul
      (ContinuousAt.comp (continuousAt_clog hp_fst) continuous_fst.continuousAt)
      continuous_snd.continuousAt

theorem continuousAt_cpow_const {a b : ℂ} (ha : a ∈ slitPlane) :
    ContinuousAt (· ^ b) a :=
  Tendsto.comp (@continuousAt_cpow (a, b) ha) (continuousAt_id.prodMk continuousAt_const)

theorem Filter.Tendsto.cpow {l : Filter α} {f g : α → ℂ} {a b : ℂ} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) (ha : a ∈ slitPlane) :
    Tendsto (fun x => f x ^ g x) l (𝓝 (a ^ b)) :=
  (@continuousAt_cpow (a, b) ha).tendsto.comp (hf.prodMk_nhds hg)

-- DISSOLVED: Filter.Tendsto.const_cpow

variable [TopologicalSpace α] {f g : α → ℂ} {s : Set α} {a : α}

nonrec theorem ContinuousWithinAt.cpow (hf : ContinuousWithinAt f s a)
    (hg : ContinuousWithinAt g s a) (h0 : f a ∈ slitPlane) :
    ContinuousWithinAt (fun x => f x ^ g x) s a :=
  hf.cpow hg h0

-- DISSOLVED: ContinuousWithinAt.const_cpow

nonrec theorem ContinuousAt.cpow (hf : ContinuousAt f a) (hg : ContinuousAt g a)
    (h0 : f a ∈ slitPlane) : ContinuousAt (fun x => f x ^ g x) a :=
  hf.cpow hg h0

-- DISSOLVED: ContinuousAt.const_cpow

theorem ContinuousOn.cpow (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (h0 : ∀ a ∈ s, f a ∈ slitPlane) : ContinuousOn (fun x => f x ^ g x) s := fun a ha =>
  (hf a ha).cpow (hg a ha) (h0 a ha)

-- DISSOLVED: ContinuousOn.const_cpow

theorem Continuous.cpow (hf : Continuous f) (hg : Continuous g)
    (h0 : ∀ a, f a ∈ slitPlane) : Continuous fun x => f x ^ g x :=
  continuous_iff_continuousAt.2 fun a => hf.continuousAt.cpow hg.continuousAt (h0 a)

-- DISSOLVED: Continuous.const_cpow

theorem ContinuousOn.cpow_const {b : ℂ} (hf : ContinuousOn f s)
    (h : ∀ a : α, a ∈ s → f a ∈ slitPlane) : ContinuousOn (fun x => f x ^ b) s :=
  hf.cpow continuousOn_const h
