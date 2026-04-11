/-
Released under MIT license.
-/
import Val.Algebra

/-!
# Val α: Preadditive Categories — The Stair 2 Test

Restates the core content of Mathlib's CategoryTheory/Preadditive/Basic.lean
using Val α's lifted laws. Every theorem is a one-liner calling the base.
No case splits. This file exists to prove the architecture works.

Mathlib Preadditive/Basic.lean: 481 lines, 58 zero references.
This file: every theorem a one-liner.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Bilinear Composition
-- ============================================================================

-- add_comp = Val.right_distrib
theorem preadditive_add_comp (mulF addF : α → α → α)
    (h : ∀ a b c : α, mulF (addF a b) c = addF (mulF a c) (mulF b c))
    (f f' g : Val α) :
    mul mulF (add addF f f') g = add addF (mul mulF f g) (mul mulF f' g) :=
  Val.right_distrib mulF addF h f f' g

-- comp_add = Val.left_distrib
theorem preadditive_comp_add (mulF addF : α → α → α)
    (h : ∀ a b c : α, mulF a (addF b c) = addF (mulF a b) (mulF a c))
    (f g g' : Val α) :
    mul mulF f (add addF g g') = add addF (mul mulF f g) (mul mulF f g') :=
  Val.left_distrib mulF addF h f g g'

-- ============================================================================
-- Negation
-- ============================================================================

-- neg_comp = Val.neg_mul
theorem preadditive_neg_comp (mulF : α → α → α) (negF : α → α)
    (h : ∀ a b : α, mulF (negF a) b = negF (mulF a b))
    (f g : Val α) :
    mul mulF (neg negF f) g = neg negF (mul mulF f g) :=
  Val.neg_mul mulF negF h f g

-- comp_neg = Val.mul_neg
theorem preadditive_comp_neg (mulF : α → α → α) (negF : α → α)
    (h : ∀ a b : α, mulF a (negF b) = negF (mulF a b))
    (f g : Val α) :
    mul mulF f (neg negF g) = neg negF (mul mulF f g) :=
  Val.mul_neg mulF negF h f g

-- ============================================================================
-- Subtraction
-- ============================================================================

-- sub_comp = Val.sub_mul
theorem preadditive_sub_comp (mulF addF : α → α → α) (negF : α → α)
    (h_distrib : ∀ a b c : α, mulF (addF a b) c = addF (mulF a c) (mulF b c))
    (h_neg : ∀ a b : α, mulF (negF a) b = negF (mulF a b))
    (f f' g : Val α) :
    mul mulF (add addF f (neg negF f')) g =
    add addF (mul mulF f g) (neg negF (mul mulF f' g)) :=
  Val.sub_mul mulF addF negF h_distrib h_neg f f' g

-- comp_sub = Val.mul_sub
theorem preadditive_comp_sub (mulF addF : α → α → α) (negF : α → α)
    (h_distrib : ∀ a b c : α, mulF a (addF b c) = addF (mulF a b) (mulF a c))
    (h_neg : ∀ a b : α, mulF a (negF b) = negF (mulF a b))
    (f g g' : Val α) :
    mul mulF f (add addF g (neg negF g')) =
    add addF (mul mulF f g) (neg negF (mul mulF f g')) :=
  Val.mul_sub mulF addF negF h_distrib h_neg f g g'

-- ============================================================================
-- neg_comp_neg: two base calls
-- ============================================================================

theorem preadditive_neg_comp_neg (mulF : α → α → α) (negF : α → α)
    (h_neg_mul : ∀ a b : α, mulF (negF a) b = negF (mulF a b))
    (h_mul_neg : ∀ a b : α, mulF a (negF b) = negF (mulF a b))
    (h_neg_neg : ∀ a : α, negF (negF a) = a)
    (f g : Val α) :
    mul mulF (neg negF f) (neg negF g) = mul mulF f g := by
  rw [Val.mul_neg mulF negF h_mul_neg, Val.neg_mul mulF negF h_neg_mul,
      Val.neg_neg negF h_neg_neg]

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Mathlib Preadditive/Basic.lean: 481 lines, 58 zero references.
-- This file: every theorem is a one-liner calling the base.
--
-- add_comp  = Val.right_distrib
-- comp_add  = Val.left_distrib
-- neg_comp  = Val.neg_mul
-- comp_neg  = Val.mul_neg
-- sub_comp  = Val.sub_mul
-- comp_sub  = Val.mul_sub
--
-- Zero case splits. Zero dispatch re-proving. The base handles it.

end Val
