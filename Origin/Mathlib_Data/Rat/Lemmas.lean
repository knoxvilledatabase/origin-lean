/-
Extracted from Data/Rat/Lemmas.lean
Genuine: 1 of 3 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Further lemmas for the Rational Numbers

-/

namespace Rat

attribute [norm_cast] num_intCast den_intCast

-- DISSOLVED: num_dvd

theorem den_dvd (a b : ℤ) : ((a /. b).den : ℤ) ∣ b := by
  by_cases b0 : b = 0; · simp [b0]
  rcases e : a /. b with ⟨n, d, h, c⟩
  rw [mk_eq_divInt,
    divInt_eq_divInt_iff b0 (ne_of_gt (Int.natCast_pos.2 (Nat.pos_of_ne_zero h)))] at e
  refine Int.dvd_natAbs.1 <| Int.natCast_dvd_natCast.2 <| c.symm.dvd_of_dvd_mul_left ?_
  rw [← Int.natAbs_mul, ← Int.natCast_dvd_natCast, Int.dvd_natAbs, ← e]; simp

-- DISSOLVED: num_den_mk
