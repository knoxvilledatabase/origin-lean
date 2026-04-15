/-
Extracted from Data/Set/Inclusion.lean
Genuine: 1 of 4 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-! # Lemmas about `inclusion`, the injection of subtypes induced by `⊆` -/

open Function

namespace Set

variable {α : Type*} {s t u : Set α}

abbrev inclusion (h : s ⊆ t) : s → t := fun x ↦ ⟨x, h x.prop⟩
