/-
Extracted from Analysis/Calculus/Deriv/Abs.lean
Genuine: 25 | Conflates: 0 | Dissolved: 20 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Derivative of the absolute value

This file compiles basic derivability properties of the absolute value, and is largely inspired
from `Mathlib.Analysis.InnerProductSpace.Calculus`, which is the analogous file for norms derived
from an inner product space.

## Tags

absolute value, derivative
-/

open Filter Real Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {n : ℕ∞} {f : E → ℝ} {f' : E →L[ℝ] ℝ} {s : Set E} {x : E}

-- DISSOLVED: contDiffAt_abs

-- DISSOLVED: ContDiffAt.abs

-- DISSOLVED: contDiffWithinAt_abs

-- DISSOLVED: ContDiffWithinAt.abs

-- DISSOLVED: contDiffOn_abs

-- DISSOLVED: ContDiffOn.abs

-- DISSOLVED: ContDiff.abs

theorem hasStrictDerivAt_abs_neg {x : ℝ} (hx : x < 0) :
    HasStrictDerivAt (|·|) (-1) x :=
  (hasStrictDerivAt_neg x).congr_of_eventuallyEq <|
    EqOn.eventuallyEq_of_mem (fun _ hy ↦ (abs_of_neg (mem_Iio.1 hy)).symm) (Iio_mem_nhds hx)

theorem hasDerivAt_abs_neg {x : ℝ} (hx : x < 0) :
    HasDerivAt (|·|) (-1) x := (hasStrictDerivAt_abs_neg hx).hasDerivAt

theorem hasStrictDerivAt_abs_pos {x : ℝ} (hx : 0 < x) :
    HasStrictDerivAt (|·|) 1 x :=
  (hasStrictDerivAt_id x).congr_of_eventuallyEq <|
    EqOn.eventuallyEq_of_mem (fun _ hy ↦ (abs_of_pos (mem_Iio.1 hy)).symm) (Ioi_mem_nhds hx)

theorem hasDerivAt_abs_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt (|·|) 1 x := (hasStrictDerivAt_abs_pos hx).hasDerivAt

-- DISSOLVED: hasStrictDerivAt_abs

-- DISSOLVED: hasDerivAt_abs

theorem HasStrictFDerivAt.abs_of_neg (hf : HasStrictFDerivAt f f' x)
    (h₀ : f x < 0) : HasStrictFDerivAt (fun x ↦ |f x|) (-f') x := by
  convert (hasStrictDerivAt_abs_neg h₀).hasStrictFDerivAt.comp x hf using 1
  ext y
  simp

theorem HasFDerivAt.abs_of_neg (hf : HasFDerivAt f f' x)
    (h₀ : f x < 0) : HasFDerivAt (fun x ↦ |f x|) (-f') x := by
  convert (hasDerivAt_abs_neg h₀).hasFDerivAt.comp x hf using 1
  ext y
  simp

theorem HasStrictFDerivAt.abs_of_pos (hf : HasStrictFDerivAt f f' x)
    (h₀ : 0 < f x) : HasStrictFDerivAt (fun x ↦ |f x|) f' x := by
  convert (hasStrictDerivAt_abs_pos h₀).hasStrictFDerivAt.comp x hf using 1
  ext y
  simp

theorem HasFDerivAt.abs_of_pos (hf : HasFDerivAt f f' x)
    (h₀ : 0 < f x) : HasFDerivAt (fun x ↦ |f x|) f' x := by
  convert (hasDerivAt_abs_pos h₀).hasFDerivAt.comp x hf using 1
  ext y
  simp

-- DISSOLVED: HasStrictFDerivAt.abs

-- DISSOLVED: HasFDerivAt.abs

theorem hasDerivWithinAt_abs_neg (s : Set ℝ) {x : ℝ} (hx : x < 0) :
    HasDerivWithinAt (|·|) (-1) s x := (hasDerivAt_abs_neg hx).hasDerivWithinAt

theorem hasDerivWithinAt_abs_pos (s : Set ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivWithinAt (|·|) 1 s x := (hasDerivAt_abs_pos hx).hasDerivWithinAt

-- DISSOLVED: hasDerivWithinAt_abs

theorem HasFDerivWithinAt.abs_of_neg (hf : HasFDerivWithinAt f f' s x)
    (h₀ : f x < 0) : HasFDerivWithinAt (fun x ↦ |f x|) (-f') s x := by
  convert (hasDerivAt_abs_neg h₀).comp_hasFDerivWithinAt x hf using 1
  simp

theorem HasFDerivWithinAt.abs_of_pos (hf : HasFDerivWithinAt f f' s x)
    (h₀ : 0 < f x) : HasFDerivWithinAt (fun x ↦ |f x|) f' s x := by
  convert (hasDerivAt_abs_pos h₀).comp_hasFDerivWithinAt x hf using 1
  simp

-- DISSOLVED: HasFDerivWithinAt.abs

theorem differentiableAt_abs_neg {x : ℝ} (hx : x < 0) :
    DifferentiableAt ℝ (|·|) x := (hasDerivAt_abs_neg hx).differentiableAt

theorem differentiableAt_abs_pos {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (|·|) x := (hasDerivAt_abs_pos hx).differentiableAt

-- DISSOLVED: differentiableAt_abs

theorem DifferentiableAt.abs_of_neg (hf : DifferentiableAt ℝ f x) (h₀ : f x < 0) :
    DifferentiableAt ℝ (fun x ↦ |f x|) x := (differentiableAt_abs_neg h₀).comp x hf

theorem DifferentiableAt.abs_of_pos (hf : DifferentiableAt ℝ f x) (h₀ : 0 < f x) :
    DifferentiableAt ℝ (fun x ↦ |f x|) x := (differentiableAt_abs_pos h₀).comp x hf

-- DISSOLVED: DifferentiableAt.abs

theorem differentiableWithinAt_abs_neg (s : Set ℝ) {x : ℝ} (hx : x < 0) :
    DifferentiableWithinAt ℝ (|·|) s x := (differentiableAt_abs_neg hx).differentiableWithinAt

theorem differentiableWithinAt_abs_pos (s : Set ℝ) {x : ℝ} (hx : 0 < x) :
    DifferentiableWithinAt ℝ (|·|) s x := (differentiableAt_abs_pos hx).differentiableWithinAt

-- DISSOLVED: differentiableWithinAt_abs

theorem DifferentiableWithinAt.abs_of_neg (hf : DifferentiableWithinAt ℝ f s x) (h₀ : f x < 0) :
    DifferentiableWithinAt ℝ (fun x ↦ |f x|) s x :=
  (differentiableAt_abs_neg h₀).comp_differentiableWithinAt x hf

theorem DifferentiableWithinAt.abs_of_pos (hf : DifferentiableWithinAt ℝ f s x) (h₀ : 0 < f x) :
    DifferentiableWithinAt ℝ (fun x ↦ |f x|) s x :=
  (differentiableAt_abs_pos h₀).comp_differentiableWithinAt x hf

-- DISSOLVED: DifferentiableWithinAt.abs

-- DISSOLVED: differentiableOn_abs

-- DISSOLVED: DifferentiableOn.abs

-- DISSOLVED: Differentiable.abs

theorem not_differentiableAt_abs_zero : ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0 := by
  intro h
  have h₁ : deriv abs (0 : ℝ) = 1 :=
    (uniqueDiffOn_Ici _ _ Set.left_mem_Ici).eq_deriv _ h.hasDerivAt.hasDerivWithinAt <|
      (hasDerivWithinAt_id _ _).congr_of_mem (fun _ h ↦ abs_of_nonneg h) Set.left_mem_Ici
  have h₂ : deriv abs (0 : ℝ) = -1 :=
    (uniqueDiffOn_Iic _ _ Set.right_mem_Iic).eq_deriv _ h.hasDerivAt.hasDerivWithinAt <|
      (hasDerivWithinAt_neg _ _).congr_of_mem (fun _ h ↦ abs_of_nonpos h) Set.right_mem_Iic
  linarith

theorem deriv_abs_neg {x : ℝ} (hx : x < 0) : deriv (|·|) x = -1 := (hasDerivAt_abs_neg hx).deriv

theorem deriv_abs_pos {x : ℝ} (hx : 0 < x) : deriv (|·|) x = 1 := (hasDerivAt_abs_pos hx).deriv

theorem deriv_abs_zero : deriv (|·|) (0 : ℝ) = 0 :=
  deriv_zero_of_not_differentiableAt not_differentiableAt_abs_zero

theorem deriv_abs (x : ℝ) : deriv (|·|) x = SignType.sign x := by
  obtain rfl | hx := eq_or_ne x 0
  · simpa using deriv_abs_zero
  · simpa [hx] using (hasDerivAt_abs hx).deriv
