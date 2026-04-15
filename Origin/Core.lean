/-
Released under MIT license.
-/

/-!
# Origin Core

Origin is wholeness. Option is the type. This file is the foundation.

One theorem. A few instances. Everything else follows.

"From wholeness comes wholeness. When wholeness is taken from wholeness,
wholeness remains." — Isha Upanishad, ~800 BCE
-/

universe u
variable {α β : Type u}

-- ============================================================================
-- The Theorem: Origin
-- ============================================================================

/-- The whole absorbs the parts. Derived from cancellation + distribution. -/
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
-- Instances: Option α gets standard notation
-- ============================================================================

instance [Mul α] : Mul (Option α) where
  mul a b := match a, b with
    | none, _ => none
    | _, none => none
    | some a, some b => some (a * b)

instance [Add α] : Add (Option α) where
  add a b := match a, b with
    | none, x => x
    | x, none => x
    | some a, some b => some (a + b)

instance [Neg α] : Neg (Option α) where
  neg a := match a with
    | none => none
    | some a => some (-a)

instance [Zero α] : Zero (Option α) where
  zero := none

-- One requires Mathlib; omitted. some(1) is the multiplicative identity.

-- ============================================================================
-- Simp Set: the ground rules
-- ============================================================================

@[simp] theorem mul_none_left [Mul α] (b : Option α) : none * b = none := by
  cases b <;> rfl
@[simp] theorem mul_none_right [Mul α] (a : Option α) : a * none = none := by
  cases a <;> rfl
@[simp] theorem mul_some [Mul α] (a b : α) : (some a : Option α) * some b = some (a * b) := rfl

@[simp] theorem add_none_left [Add α] (b : Option α) : none + b = b := by
  cases b <;> rfl
@[simp] theorem add_none_right [Add α] (a : Option α) : a + none = a := by
  cases a <;> rfl
@[simp] theorem add_some [Add α] (a b : α) : (some a : Option α) + some b = some (a + b) := rfl

@[simp] theorem neg_none [Neg α] : -(none : Option α) = none := rfl
@[simp] theorem neg_some [Neg α] (a : α) : -(some a : Option α) = some (-a) := rfl

-- ============================================================================
-- Cross-Type Lift (for physics, tensors)
-- ============================================================================

variable {γ : Type u}

def liftBin₂ (f : α → β → γ) : Option α → Option β → Option γ
  | none, _ => none
  | _, none => none
  | some a, some b => some (f a b)

@[simp] theorem liftBin₂_none_left (f : α → β → γ) (b : Option β) :
    liftBin₂ f none b = none := by cases b <;> rfl
@[simp] theorem liftBin₂_none_right (f : α → β → γ) (a : Option α) :
    liftBin₂ f a none = none := by cases a <;> rfl
@[simp] theorem liftBin₂_some (f : α → β → γ) (a : α) (b : β) :
    liftBin₂ f (some a) (some b) = some (f a b) := rfl

-- ============================================================================
-- The No-Some-Fixed-Point Theorem (for logic)
-- ============================================================================

/-- If f has no fixed point on α, no some value is a fixed point
    of Option.map f. The formal system can't hold its own ground. -/
theorem no_some_fixed_point
    (f : α → α) (hf : ∀ a : α, f a ≠ a)
    (v : Option α) (hv : v.map f = v) : v = none := by
  cases v with
  | none => rfl
  | some a => simp at hv; exact absurd hv (hf a)

-- ============================================================================
-- That's it.
-- ============================================================================

-- One theorem (origin). Instances for *, +, -. A simp set. liftBin₂.
-- no_some_fixed_point. Standard notation. Everything else follows.
--
-- none is the whole. some is a part. * + - work on Option with
-- standard notation. The ground absorbs. The parts compute.
--
-- Clone it. Build it. Use it.
--
-- lake build Origin.Core
