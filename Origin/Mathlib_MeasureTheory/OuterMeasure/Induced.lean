/-
Extracted from MeasureTheory/OuterMeasure/Induced.lean
Genuine: 5 of 7 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Induced Outer Measure

We can extend a function defined on a subset of `Set α` to an outer measure.
The underlying function is called `extend`, and the measure it induces is called
`inducedOuterMeasure`.

Some lemmas below are proven twice, once in the general case, and once where the function `m`
is only defined on measurable sets (i.e. when `P = MeasurableSet`). In the latter cases, we can
remove some hypotheses in the statement. The general version has the same name, but with a prime
at the end.

## Tags

outer measure

-/

noncomputable section

open Set Function Filter

open scoped NNReal Topology ENNReal

namespace MeasureTheory

open OuterMeasure

section Extend

variable {R α : Type*} {P : α → Prop}

variable (m : ∀ s : α, P s → ℝ≥0∞)

def extend (s : α) : ℝ≥0∞ :=
  ⨅ h : P s, m s h

theorem extend_eq {s : α} (h : P s) : extend m s = m s h := by simp [extend, h]

theorem extend_eq_top {s : α} (h : ¬P s) : extend m s = ∞ := by simp [extend, h]

-- DISSOLVED: smul_extend

-- DISSOLVED: ennreal_smul_extend

theorem le_extend {s : α} (h : P s) : m s h ≤ extend m s := by
  simp only [extend, le_iInf_iff]
  intro
  rfl

theorem extend_congr {β : Type*} {Pb : β → Prop} {mb : ∀ s : β, Pb s → ℝ≥0∞} {sa : α} {sb : β}
    (hP : P sa ↔ Pb sb) (hm : ∀ (ha : P sa) (hb : Pb sb), m sa ha = mb sb hb) :
    extend m sa = extend mb sb :=
  iInf_congr_Prop hP fun _h => hm _ _
