/-
Extracted from Algebra/Ring/Torsion.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Torsion-free rings

A characteristic zero domain is torsion-free.
-/

namespace IsDomain

-- INSTANCE (free from Core): (R

end IsDomain

namespace MonoidHom

variable {R M : Type*} [Ring R] [Monoid M] [IsMulTorsionFree M] (f : R →* M)

lemma map_neg_one : f (-1) = 1 :=
  (pow_eq_one_iff_left (Nat.succ_ne_zero 1)).1 <| by rw [← map_pow, neg_one_sq, map_one]
