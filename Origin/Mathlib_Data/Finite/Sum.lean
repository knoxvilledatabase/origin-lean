/-
Extracted from Data/Finite/Sum.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Finiteness of sum types
-/

variable {α β : Type*}

namespace Finite

-- INSTANCE (free from Core): [Finite

theorem sum_left (β) [Finite (α ⊕ β)] : Finite α :=
  of_injective (Sum.inl : α → α ⊕ β) Sum.inl_injective

theorem sum_right (α) [Finite (α ⊕ β)] : Finite β :=
  of_injective (Sum.inr : β → α ⊕ β) Sum.inr_injective

-- INSTANCE (free from Core): {α

theorem psum_left {α β : Sort*} [Finite (α ⊕' β)] : Finite α :=
  of_injective (PSum.inl : α → α ⊕' β) PSum.inl_injective

theorem psum_right {α β : Sort*} [Finite (α ⊕' β)] : Finite β :=
  of_injective (PSum.inr : β → α ⊕' β) PSum.inr_injective

end Finite
