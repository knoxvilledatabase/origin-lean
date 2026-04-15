/-
Extracted from Data/Set/Disjoint.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Theorems about the `Disjoint` relation on `Set`.
-/

assert_not_exists HeytingAlgebra RelIso

/-! ### Set coercion to a type -/

open Function

universe u v

namespace Set

variable {α : Type u} {s t u s₁ s₂ t₁ t₂ : Set α}

/-! ### Disjointness -/

protected theorem disjoint_iff : Disjoint s t ↔ s ∩ t ⊆ ∅ :=
  disjoint_iff_inf_le

theorem disjoint_iff_inter_eq_empty : Disjoint s t ↔ s ∩ t = ∅ :=
  disjoint_iff

theorem _root_.Disjoint.inter_eq : Disjoint s t → s ∩ t = ∅ :=
  Disjoint.eq_bot
