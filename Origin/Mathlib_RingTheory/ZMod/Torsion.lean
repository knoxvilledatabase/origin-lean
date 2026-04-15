/-
Extracted from RingTheory/ZMod/Torsion.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Torsion group of `ZMod p` for prime `p`

This file shows that the `ZMod p` has `p - 1` roots-of-unity.

-/

namespace ZMod

lemma rootsOfUnity_eq_top {p : ℕ} [Fact p.Prime] :
    (rootsOfUnity (p - 1) (ZMod p)) = ⊤ := by
  ext
  simpa [Units.ext_iff] using pow_card_sub_one_eq_one (Units.ne_zero _)

-- INSTANCE (free from Core): {p

end ZMod
