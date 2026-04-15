/-
Extracted from Algebra/CharP/Subring.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Characteristic of subrings
-/

universe u v

namespace CharP

-- INSTANCE (free from Core): subsemiring

-- INSTANCE (free from Core): subring

-- INSTANCE (free from Core): subring'

theorem charP_center_iff {R : Type u} [Ring R] {p : ℕ} :
    CharP (Subring.center R) p ↔ CharP R p :=
  (algebraMap (Subring.center R) R).charP_iff Subtype.val_injective p

end CharP

namespace ExpChar

theorem expChar_center_iff {R : Type u} [Ring R] {p : ℕ} :
    ExpChar (Subring.center R) p ↔ ExpChar R p :=
  (algebraMap (Subring.center R) R).expChar_iff Subtype.val_injective p

end ExpChar
