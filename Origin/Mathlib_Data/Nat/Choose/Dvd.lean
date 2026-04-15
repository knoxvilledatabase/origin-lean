/-
Extracted from Data/Nat/Choose/Dvd.lean
Genuine: 2 | Conflates: 0 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Factorial

/-!
# Divisibility properties of binomial coefficients
-/

namespace Nat

namespace Prime

variable {p a b k : ℕ}

theorem dvd_choose_add (hp : Prime p) (hap : a < p) (hbp : b < p) (h : p ≤ a + b) :
    p ∣ choose (a + b) a := by
  have h₁ : p ∣ (a + b)! := hp.dvd_factorial.2 h
  rw [← add_choose_mul_factorial_mul_factorial, ← choose_symm_add, hp.dvd_mul, hp.dvd_mul,
    hp.dvd_factorial, hp.dvd_factorial] at h₁
  exact (h₁.resolve_right hbp.not_le).resolve_right hap.not_le

lemma dvd_choose (hp : Prime p) (ha : a < p) (hab : b - a < p) (h : p ≤ b) : p ∣ choose b a :=
  have : a + (b - a) = b := Nat.add_sub_of_le (ha.le.trans h)
  this ▸ hp.dvd_choose_add ha hab (this.symm ▸ h)

-- DISSOLVED: dvd_choose_self

end Prime

end Nat
