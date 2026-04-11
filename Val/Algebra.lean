/-
Released under MIT license.
-/
import Val.Foundation

/-!
# Val α: Lifted Laws — The Abstract Base Model

Every algebraic law that α satisfies is lifted to Val α here.
Proved once. Called everywhere. No domain file re-proves these.

The pattern: cases <;> simp <;> apply h

Origin cases: simp closes them (Foundation's simp lemmas).
Non-origin cases: simp reduces to constructor(expression) = constructor(expression).
Then apply h uses α's law inside the constructor.

Explicit function parameters. Zero typeclasses. Zero Mathlib.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Associativity
-- ============================================================================

theorem mul_assoc (f : α → α → α)
    (h : ∀ a b c : α, f (f a b) c = f a (f b c))
    (a b c : Val α) : mul f (mul f a b) c = mul f a (mul f b c) := by
  cases a <;> cases b <;> cases c <;> simp [mul] <;> apply h

theorem add_assoc (f : α → α → α)
    (h : ∀ a b c : α, f (f a b) c = f a (f b c))
    (a b c : Val α) : add f (add f a b) c = add f a (add f b c) := by
  cases a <;> cases b <;> cases c <;> simp [add] <;> apply h

-- ============================================================================
-- Commutativity
-- ============================================================================

theorem mul_comm (f : α → α → α)
    (h : ∀ a b : α, f a b = f b a)
    (a b : Val α) : mul f a b = mul f b a := by
  cases a <;> cases b <;> simp [mul] <;> apply h

theorem add_comm (f : α → α → α)
    (h : ∀ a b : α, f a b = f b a)
    (a b : Val α) : add f a b = add f b a := by
  cases a <;> cases b <;> simp [add] <;> apply h

-- ============================================================================
-- Distributivity
-- ============================================================================

theorem left_distrib (mulF addF : α → α → α)
    (h : ∀ a b c : α, mulF a (addF b c) = addF (mulF a b) (mulF a c))
    (a b c : Val α) : mul mulF a (add addF b c) = add addF (mul mulF a b) (mul mulF a c) := by
  cases a <;> cases b <;> cases c <;> simp [mul, add] <;> apply h

theorem right_distrib (mulF addF : α → α → α)
    (h : ∀ a b c : α, mulF (addF a b) c = addF (mulF a c) (mulF b c))
    (a b c : Val α) : mul mulF (add addF a b) c = add addF (mul mulF a c) (mul mulF b c) := by
  cases a <;> cases b <;> cases c <;> simp [mul, add] <;> apply h

-- ============================================================================
-- Identity Laws
-- ============================================================================

theorem mul_one (f : α → α → α) (one : α)
    (h : ∀ a : α, f a one = a)
    (a : Val α) : mul f a (contents one) = a := by
  cases a <;> simp [mul, h]

theorem one_mul (f : α → α → α) (one : α)
    (h : ∀ a : α, f one a = a)
    (a : Val α) : mul f (contents one) a = a := by
  cases a <;> simp [mul, h]

theorem add_zero (f : α → α → α) (zero : α)
    (h : ∀ a : α, f a zero = a)
    (a : Val α) : add f a (contents zero) = a := by
  cases a <;> simp [add, h]

theorem zero_add (f : α → α → α) (zero : α)
    (h : ∀ a : α, f zero a = a)
    (a : Val α) : add f (contents zero) a = a := by
  cases a <;> simp [add, h]

-- ============================================================================
-- Negation Laws
-- ============================================================================

theorem neg_mul (mulF : α → α → α) (negF : α → α)
    (h : ∀ a b : α, mulF (negF a) b = negF (mulF a b))
    (a b : Val α) : mul mulF (neg negF a) b = neg negF (mul mulF a b) := by
  cases a <;> cases b <;> simp [mul, neg] <;> apply h

theorem mul_neg (mulF : α → α → α) (negF : α → α)
    (h : ∀ a b : α, mulF a (negF b) = negF (mulF a b))
    (a b : Val α) : mul mulF a (neg negF b) = neg negF (mul mulF a b) := by
  cases a <;> cases b <;> simp [mul, neg] <;> apply h

theorem neg_neg (negF : α → α)
    (h : ∀ a : α, negF (negF a) = a)
    (a : Val α) : neg negF (neg negF a) = a := by
  cases a <;> simp [neg, h]

-- ============================================================================
-- Subtraction Laws (derived from distributivity + negation)
-- ============================================================================

theorem sub_mul (mulF addF : α → α → α) (negF : α → α)
    (h_distrib : ∀ a b c : α, mulF (addF a b) c = addF (mulF a c) (mulF b c))
    (h_neg : ∀ a b : α, mulF (negF a) b = negF (mulF a b))
    (a b c : Val α) :
    mul mulF (add addF a (neg negF b)) c =
    add addF (mul mulF a c) (neg negF (mul mulF b c)) := by
  rw [right_distrib mulF addF h_distrib, neg_mul mulF negF h_neg]

theorem mul_sub (mulF addF : α → α → α) (negF : α → α)
    (h_distrib : ∀ a b c : α, mulF a (addF b c) = addF (mulF a b) (mulF a c))
    (h_neg : ∀ a b : α, mulF a (negF b) = negF (mulF a b))
    (a b c : Val α) :
    mul mulF a (add addF b (neg negF c)) =
    add addF (mul mulF a b) (neg negF (mul mulF a c)) := by
  rw [left_distrib mulF addF h_distrib, mul_neg mulF negF h_neg]

-- ============================================================================
-- Inverse Laws
-- ============================================================================

theorem mul_inv (mulF : α → α → α) (invF : α → α) (one : α)
    (h : ∀ a : α, mulF a (invF a) = one)
    (a : α) : mul mulF (contents a) (inv invF (contents a)) = contents one := by
  simp [mul, inv, h]

theorem inv_mul (mulF : α → α → α) (invF : α → α) (one : α)
    (h : ∀ a : α, mulF (invF a) a = one)
    (a : α) : mul mulF (inv invF (contents a)) (contents a) = contents one := by
  simp [mul, inv, h]

theorem inv_inv (invF : α → α)
    (h : ∀ a : α, invF (invF a) = a)
    (a : Val α) : inv invF (inv invF a) = a := by
  cases a <;> simp [inv, h]

-- ============================================================================
-- Additive Inverse Laws
-- ============================================================================

theorem add_neg (addF : α → α → α) (negF : α → α) (zero : α)
    (h : ∀ a : α, addF a (negF a) = zero)
    (a : α) : add addF (contents a) (neg negF (contents a)) = contents zero := by
  simp [add, neg, h]

theorem neg_add (addF : α → α → α) (negF : α → α) (zero : α)
    (h : ∀ a : α, addF (negF a) a = zero)
    (a : α) : add addF (neg negF (contents a)) (contents a) = contents zero := by
  simp [add, neg, h]

-- ============================================================================
-- Faithful Embedding
-- ============================================================================

-- contents preserves all operations (from Foundation's simp lemmas):
--   mul f (contents a) (contents b) = contents (f a b)
--   add f (contents a) (contents b) = contents (f a b)
--   neg f (contents a) = contents (f a)
--   inv f (contents a) = contents (f a)
-- All by simp. The bucket is transparent.

-- contents is injective (from Foundation):
--   contents_injective, contents_inj

-- ============================================================================
-- Sort Result of Any Operation
-- ============================================================================

-- The sort of mul f a b is ALWAYS determined by the sorts of a and b.
-- No hypothesis needed. The type carries it.

theorem mul_sort (f : α → α → α) (a b : Val α) :
    (a = origin ∨ b = origin → mul f a b = origin) ∧
    (∀ va vb, a = contents va → b = contents vb → mul f a b = contents (f va vb)) ∧
    (∀ va vb, a = container va → b = container vb → mul f a b = container (f va vb)) ∧
    (∀ va vb, a = container va → b = contents vb → mul f a b = container (f va vb)) ∧
    (∀ va vb, a = contents va → b = container vb → mul f a b = container (f va vb)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; cases h with | inl h => subst h; simp | inr h => subst h; simp
  · intros va vb ha hb; subst ha; subst hb; rfl
  · intros va vb ha hb; subst ha; subst hb; rfl
  · intros va vb ha hb; subst ha; subst hb; rfl
  · intros va vb ha hb; subst ha; subst hb; rfl

end Val
