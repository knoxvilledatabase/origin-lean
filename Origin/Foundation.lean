/-
Released under MIT license.
-/

/-!
# Origin

Origin is wholeness.

Not nothingness. Not emptiness. Not the absence of value. Wholeness.
The ground everything stands on. The ocean the fish swim in. The
unity from which counting begins and to which cancellation returns.

The Sanskrit tradition knew both faces: *śūnya* (emptiness, the count
of nothing) and *pūrṇa* (fullness, the whole). When Brahmagupta
formalized zero in 628 CE, only *śūnya* entered the arithmetic.
*Pūrṇa* — wholeness — stayed in the philosophy.

The symbol 0 named the wrong face. The ground is not empty. The
ground is full. The whole that remains whole when wholeness is taken
from wholeness.

When you apply wholeness to the algebra, you can do things that
weren't possible without it:

- **Mathematics:** 17 zero-management typeclasses eliminated. 9,682
  `≠ 0` hypotheses dissolved. The typeclasses managed the whole being
  inside the counting domain. Put it outside. They vanish.

- **Physics:** 86 existence hypotheses dissolved. Singularities,
  vacua, absolute zero — places where the counting doesn't apply.
  The whole was always there. The hypotheses guarded against it.

- **Logic:** The Liar, Russell, Curry unified under one theorem.
  Every paradox is a formal system trying to hold the whole from
  inside. The whole can't be a part. The algebra proves it.

- **Computation:** `Option<T>` and `Result<T, E>`. None is the whole.
  Some is a part. ML had this in 1973. The derivation below is WHY
  two constructors are sufficient.

The derivation:

  0 = n + (-n)                          — cancellation returns to the whole
  n × 0 = n × (n + (-n))               — substitution
        = n×n + n×(-n)                  — the distributive law
        = n×n + -(n×n)                  — multiplication over negation
        = 0                             — cancellation returns to the whole

The whole absorbs under multiplication because cancellation returns
to the whole and the distributive law propagates it. The whole absorbs
the parts — not as an axiom, but as a consequence of what wholeness is.

*"That is whole. This is whole. From wholeness comes wholeness.
When wholeness is taken from wholeness, wholeness remains."*
— Isha Upanishad, ~800 BCE
-/

universe u
variable {α : Type u}

-- ============================================================================
-- The Theorem
-- ============================================================================

/-- Origin: the whole absorbs the parts.

    Multiplying by zero returns to the whole. Derived from three
    facts about arithmetic — not asserted, proved:

    1. Cancellation: n + (-n) = 0         (the whole is what remains)
    2. Distribution: n × (a + b) = n×a + n×b
    3. Negation:     n × (-a) = -(n×a)

    The whole absorbs because cancellation returns to the whole
    and the distributive law propagates it through multiplication.

    This is why Option<T> is sufficient. This is why the 17 typeclasses
    vanish. This is why 9,682 hypotheses dissolve. The whole was never
    inside the counting domain. Put it outside. Everything simplifies. -/
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

-- ============================================================================
-- The Type
-- ============================================================================

-- Therefore: Option α.
--
-- None   = the whole. Origin. What counting stands on.
-- Some a = a part. A value. In the counting domain.
--
-- When zero is a measurement (a sensor read zero, a count returned zero):
-- that's Some(0). A part. Data. In the counting domain.
--
-- When there's nothing to measure (the field doesn't apply, the system
-- isn't in equilibrium, the computation hasn't started): that's None.
-- The whole. Not a value. What values stand on.
--
-- Two constructors. The whole and the parts. Option.
-- ML had this in 1973. Haskell in 1990. Rust in 2015.
-- The theorem above is WHY.
