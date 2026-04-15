/-
Extracted from Data/Finite/Prod.lean
Genuine: 3 of 9 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Finiteness of products
-/

assert_not_exists IsOrderedRing MonoidWithZero

variable {α β : Type*}

namespace Finite

-- INSTANCE (free from Core): [Finite

-- INSTANCE (free from Core): {α

theorem prod_left (β) [Finite (α × β)] [Nonempty β] : Finite α :=
  of_surjective (Prod.fst : α × β → α) Prod.fst_surjective

theorem prod_right (α) [Finite (α × β)] [Nonempty α] : Finite β :=
  of_surjective (Prod.snd : α × β → β) Prod.snd_surjective

end Finite

lemma Prod.finite_iff [Nonempty α] [Nonempty β] : Finite (α × β) ↔ Finite α ∧ Finite β where
  mp _ := ⟨.prod_left β, .prod_right α⟩
  mpr | ⟨_, _⟩ => inferInstance

-- INSTANCE (free from Core): Pi.finite

-- INSTANCE (free from Core): Function.Embedding.finite

-- INSTANCE (free from Core): Equiv.finite_right

-- INSTANCE (free from Core): Equiv.finite_left
