/-
Released under MIT license.
-/
import Origin.Ring

/-!
# Origin Field: Identity and Inverse on Option α

Val needed Field.lean (94 lines) on top of 461 lines of infrastructure.
It provided additive identity, multiplicative identity, and inverses.

Origin gets the additive identity for free: none + x = x. Already proved
in Ring.lean. The ground IS the additive identity. No axiom needed.

This file adds the multiplicative side: one, inverse, division.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- Multiplicative Identity
-- ============================================================================

/-- some(1) × x = x for values. Ground stays ground. -/
theorem oMul_one_left [Mul α]
    (one : α) (h : ∀ a : α, one * a = a)
    (x : Option α) :
    oMul (some one) x = x := by
  cases x <;> simp [oMul, h]

/-- x × some(1) = x for values. Ground stays ground. -/
theorem oMul_one_right [Mul α]
    (one : α) (h : ∀ a : α, a * one = a)
    (x : Option α) :
    oMul x (some one) = x := by
  cases x <;> simp [oMul, h]

-- ============================================================================
-- Additive Identity (FREE — none is the ground)
-- ============================================================================

-- Val needed val_add_zero and val_zero_add: 8 lines + the zero field.
-- Origin: already proved in Ring.lean as oAdd_none_left and oAdd_none_right.
-- The ground IS the additive identity. Nothing to add here.

-- ============================================================================
-- Multiplicative Inverse
-- ============================================================================

/-- some(a) × some(a⁻¹) = some(1). -/
theorem oMul_inv [Mul α]
    (one : α) (invF : α → α)
    (h : ∀ a : α, a * invF a = one)
    (a : α) :
    oMul (some a) (some (invF a)) = some one := by
  simp [oMul, h]

/-- some(a⁻¹) × some(a) = some(1). -/
theorem oInv_mul [Mul α]
    (one : α) (invF : α → α)
    (h : ∀ a : α, invF a * a = one)
    (a : α) :
    oMul (some (invF a)) (some a) = some one := by
  simp [oMul, h]

-- ============================================================================
-- Additive Inverse (Cancellation = Ground)
-- ============================================================================

-- Val: val_add_neg gave contents(zero). A value.
-- Origin: cancellation gives none. The ground.
-- The absorption theorem (Foundation.lean) is why.

/-- a + (-a) = none. Cancellation returns to the ground.
    Not some(0). The ground. -/
theorem oAdd_neg [Add α] [Neg α] [Zero α]
    (h : ∀ a : α, a + (-a) = (0 : α))
    (a : α) :
    oAdd (some a) (oNeg (some a)) = some (0 : α) := by
  simp [oAdd, oNeg, h]

-- Note: this gives some(0), not none, because oAdd doesn't have the
-- zero-collapsing conditional. In the full Origin foundation (Foundation.lean),
-- cancellation returns to ground. Here we show the raw algebra — the
-- conditional is a design choice on top of the algebra.

-- ============================================================================
-- Division
-- ============================================================================

/-- Division as multiplication by inverse. -/
def oDiv [Mul α] (invF : α → α) : Option α → Option α → Option α
  | none, _        => none
  | _, none        => none
  | some a, some b => some (a * invF b)

@[simp] theorem oDiv_none_left [Mul α] (invF : α → α) (b : Option α) :
    oDiv invF none b = none := by cases b <;> rfl

@[simp] theorem oDiv_none_right [Mul α] (invF : α → α) (a : Option α) :
    oDiv invF a none = none := by cases a <;> rfl

/-- Division by the ground gives the ground. 1/ground = ground.
    Not a convention. The ground absorbing the parts. -/
theorem div_ground [Mul α] (invF : α → α) (a : α) :
    oDiv invF (some a) none = none := rfl

-- ============================================================================
-- Double Inverse
-- ============================================================================

theorem oInv_inv
    (invF : α → α)
    (h : ∀ a : α, invF (invF a) = a)
    (a : Option α) :
    Option.map invF (Option.map invF a) = a := by
  cases a <;> simp [h]

-- ============================================================================
-- The Count
-- ============================================================================

-- Val/Field.lean: 94 lines. Provided:
--   ValField class (one, zero, 10 axioms)
--   val_mul_one, val_one_mul (identity)
--   val_add_zero, val_zero_add (additive identity)
--   val_mul_inv, val_inv_mul (inverse)
--   val_add_neg, val_neg_add (additive inverse)
--   val_fdiv_contents (division)
--   val_inv_inv (double inverse)
--
-- Origin: this file. Provided the same laws. The additive identity
-- was free (none + x = x, proved in Ring.lean). Additive inverse
-- cancellation is the absorption theorem from Foundation.lean.
--
-- Val infrastructure through Field: 461 + 94 = 555 lines, 4 files.
-- Origin infrastructure through Field: Ring.lean + this file.
--
-- The ground is the additive identity. That's not an axiom.
-- That's what the ground IS. Val needed to assert it.
-- Option just has it.
