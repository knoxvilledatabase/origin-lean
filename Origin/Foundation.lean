/-
Released under MIT license.
-/

/-!
# Origin Foundation

The whole. And the parts. Everything else follows.

The ground is not nothing. The ground is the whole — the unity from
which counting begins. The symbol 0 named the wrong face. The Sanskrit
tradition had both: śūnya (emptiness) and pūrṇa (fullness, wholeness).
Brahmagupta formalized śūnya and left pūrṇa in the philosophy.

The ground absorbs under multiplication. Not as an axiom. As a
consequence of three facts about arithmetic:

  1. Cancellation returns to the ground: a + (-a) = 0
  2. Multiplication distributes over addition
  3. Multiplication distributes over negation

From these, the four-step derivation:

  0 = n + (-n)                          (cancellation)
  n × 0 = n × (n + (-n))               (substitution)
  n × (n + (-n)) = n×n + n×(-n)        (distributive law)
               = n×n + -(n×n)          (mul over negation)
               = 0                      (cancellation)

Therefore: n × 0 = 0. The ground absorbs. QED.

The 17 typeclasses managed the whole being inside the counting domain.
Put it outside. They vanish.

Option α is the type. None is the ground. Some is a value.
ML had this in 1973. The derivation is WHY.

"From wholeness comes wholeness. When wholeness is taken from wholeness,
wholeness remains." — Isha Upanishad, ~800 BCE
-/

universe u
variable {α : Type u}

-- ============================================================================
-- The Derivation
-- ============================================================================

/-- The ground absorbs under multiplication. Derived from three premises.

    1. Cancellation: a + (-a) = 0
    2. Distributive law: a × (b + c) = a×b + a×c
    3. Mul over negation: a × (-b) = -(a×b)

    Four steps. The rest is algebra. -/
theorem absorption [Add α] [Mul α] [Neg α]
    (zero : α)
    (add_neg : ∀ a : α, a + (-a) = zero)
    (distrib : ∀ a b c : α, a * (b + c) = a * b + a * c)
    (mul_neg : ∀ a b : α, a * (-b) = -(a * b))
    (n : α) : n * zero = zero :=
  calc n * zero
      _ = n * (n + (-n))           := by rw [add_neg]
      _ = n * n + n * (-n)         := by rw [distrib]
      _ = n * n + -(n * n)         := by rw [mul_neg]
      _ = zero                     := by rw [add_neg]

-- ============================================================================
-- The Type
-- ============================================================================

-- Therefore: Option α.
--
-- None  = the ground. The whole. The additive identity.
--         What counting stands on. Not a value.
--
-- Some a = a value. A part. In the counting domain.
--          Including zero when zero is a measurement result.
--
-- The 17 typeclasses managed the whole being inside the counting domain.
-- Put it outside. They vanish. Not reduced. Not consolidated. Gone.
-- Because the problem they solved was never a real problem — it was
-- a consequence of putting the whole where it doesn't belong.

-- ============================================================================
-- The Connection
-- ============================================================================

-- Val α (three constructors) was the proof of concept.
-- Origin (two constructors) is the derivation of why it works.
-- Option α (the standard library) is the implementation.
--
-- They are the same insight at three levels:
--   Val:    "separate the ground from the counting domain"
--   Origin: "the ground absorbs because cancellation + distribution force it"
--   Option: None | Some. The whole, or a part.
--
-- The shepherd always had two things. The ground. His hand.
-- The apple is what's in the hand. Zero is the empty hand.
-- The ground is what the hand rests on. You can't hold the ground.
-- The algebra proves you can't. The type system enforces it.
--
-- 1,400 years. 97 patches. 17 typeclasses. One derivation.
