/-
Extracted from Algebra/Algebra/ZMod.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The `ZMod n`-algebra structure on rings whose characteristic divides `n`
-/

assert_not_exists TwoSidedIdeal

namespace ZMod

variable (R : Type*) [Ring R]

-- INSTANCE (free from Core): (p

variable {n : ℕ} (m : ℕ) [CharP R m]

abbrev algebra' (h : m ∣ n) : Algebra (ZMod n) R where
  algebraMap := ZMod.castHom h R
  smul := fun a r => cast a * r
  commutes' := fun a r =>
    show (cast a * r : R) = r * cast a by
      rcases ZMod.intCast_surjective a with ⟨k, rfl⟩
      change ZMod.castHom h R k * r = r * ZMod.castHom h R k
      rw [map_intCast, Int.cast_comm]
  smul_def' := fun _ _ => rfl

end

abbrev algebra (p : ℕ) [CharP R p] : Algebra (ZMod p) R :=
  algebra' R p dvd_rfl

set_option backward.isDefEq.respectTransparency false in
