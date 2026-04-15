/-
Extracted from MeasureTheory/Measure/MutuallySingular.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Mutually singular measures

Two measures `μ`, `ν` are said to be mutually singular (`MeasureTheory.Measure.MutuallySingular`,
localized notation `μ ⟂ₘ ν`) if there exists a measurable set `s` such that `μ s = 0` and
`ν sᶜ = 0`. The measurability of `s` is an unnecessary assumption (see
`MeasureTheory.Measure.MutuallySingular.mk`) but we keep it because this way `rcases (h : μ ⟂ₘ ν)`
gives us a measurable set and usually it is easy to prove measurability.

In this file we define the predicate `MeasureTheory.Measure.MutuallySingular` and prove basic
facts about it.

## Tags

measure, mutually singular
-/

open Set

open MeasureTheory NNReal ENNReal Filter

namespace MeasureTheory

namespace Measure

variable {α : Type*} {m0 : MeasurableSpace α} {μ μ₁ μ₂ ν ν₁ ν₂ : Measure α}

def MutuallySingular {_ : MeasurableSpace α} (μ ν : Measure α) : Prop :=
  ∃ s : Set α, MeasurableSet s ∧ μ s = 0 ∧ ν sᶜ = 0
