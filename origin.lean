/-
Released under MIT license.
-/

/-!
# Origin

The whole absorbs the parts. Not as an axiom — as a consequence
of cancellation and the distributive law.

"From wholeness comes wholeness. When wholeness is taken from
wholeness, wholeness remains." — Isha Upanishad, ~800 BCE
-/

universe u
variable {α : Type u}

/-- The whole absorbs the parts. Derived from cancellation + distribution.

    Three premises. One derivation. The ground absorbs under
    multiplication BECAUSE cancellation returns to the ground
    and the distributive law propagates it. -/
theorem origin [Add α] [Mul α] [Neg α]
    (zero : α)
    (cancel : ∀ a : α, a + (-a) = zero)
    (distrib : ∀ a b c : α, a * (b + c) = a * b + a * c)
    (mul_neg : ∀ a b : α, a * (-b) = -(a * b))
    (n : α) : n * zero = zero :=
  calc n * zero
      _ = n * (n + (-n))           := by rw [cancel]
      _ = n * n + n * (-n)         := by rw [distrib]
      _ = n * n + -(n * n)         := by rw [mul_neg]
      _ = zero                     := by rw [cancel]
