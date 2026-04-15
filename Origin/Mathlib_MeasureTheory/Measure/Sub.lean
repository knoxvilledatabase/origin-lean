/-
Extracted from MeasureTheory/Measure/Sub.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Subtraction of measures

In this file we define `μ - ν` to be the least measure `τ` such that `μ ≤ τ + ν`.
It is equivalent to `(μ - ν) ⊔ 0` if `μ` and `ν` were signed measures.
Compare with `ENNReal.instSub`.
Specifically, note that if you have `α = {1,2}`, and `μ {1} = 2`, `μ {2} = 0`, and
`ν {2} = 2`, `ν {1} = 0`, then `(μ - ν) {1, 2} = 2`. However, if `μ ≤ ν`, and
`ν univ ≠ ∞`, then `(μ - ν) + ν = μ`.
-/

open Set

namespace MeasureTheory

namespace Measure

-- INSTANCE (free from Core): instSub

variable {α : Type*} {m : MeasurableSpace α} {μ ν ξ : Measure α} {s : Set α}

theorem sub_le_of_le_add {d} (h : μ ≤ d + ν) : μ - ν ≤ d :=
  sInf_le h

theorem sub_eq_zero_of_le (h : μ ≤ ν) : μ - ν = 0 :=
  nonpos_iff_eq_zero'.1 <| sub_le_of_le_add <| by rwa [zero_add]

theorem sub_le : μ - ν ≤ μ :=
  sub_le_of_le_add <| Measure.le_add_right le_rfl
