/-
Extracted from Data/Seq/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Basic properties of sequences (possibly infinite lists)

This file provides some basic lemmas about possibly infinite lists represented by the
type `Stream'.Seq`.
-/

universe u v w

namespace Stream'

namespace Seq

variable {α : Type u} {β : Type v} {γ : Type w}

section length

theorem length'_of_terminates {s : Seq α} (h : s.Terminates) :
    s.length' = s.length h := by
  simp [length', h]

theorem length'_of_not_terminates {s : Seq α} (h : ¬ s.Terminates) :
    s.length' = ⊤ := by
  simp [length', h]

set_option linter.flexible false in -- simp followed by exact rfl
