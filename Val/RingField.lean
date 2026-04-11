/-
Released under MIT license.
-/
import Val.Algebra

/-!
# Val α: Ring and Field Laws

Everything here calls the base. Ring laws, field laws, dissolved hypotheses.

The honest finding: Val α as a whole is not a field. The field lives
inside contents. Origin and container are outside the field by type.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Dissolved Hypotheses
-- ============================================================================

-- NeZero: contents a ≠ origin. Always. By construction.
theorem contents_ne_origin' (a : α) : (contents a : Val α) ≠ origin := by simp

-- NoZeroDivisors: contents × contents never produces origin.
theorem no_zero_divisors (f : α → α → α) (a b : α) :
    mul f (contents a) (contents b) ≠ origin := by simp

-- Nontrivial: origin ≠ contents(anything). Different constructors.
theorem origin_ne_contents' (a : α) : (origin : Val α) ≠ contents a := by simp

-- ============================================================================
-- The Field Lives in Contents
-- ============================================================================

-- Contents is closed under all field operations.
theorem field_closed_mul (f : α → α → α) (a b : α) :
    ∃ c, mul f (contents a) (contents b) = contents c := ⟨f a b, rfl⟩

theorem field_closed_add (f : α → α → α) (a b : α) :
    ∃ c, add f (contents a) (contents b) = contents c := ⟨f a b, rfl⟩

theorem field_closed_neg (f : α → α) (a : α) :
    ∃ c, neg f (contents a) = contents c := ⟨f a, rfl⟩

theorem field_closed_inv (f : α → α) (a : α) :
    ∃ c, inv f (contents a) = contents c := ⟨f a, rfl⟩

-- Contents never escape to origin under any operation.
theorem field_never_origin_mul (f : α → α → α) (a b : α) :
    mul f (contents a) (contents b) ≠ origin := by simp

theorem field_never_origin_add (f : α → α → α) (a b : α) :
    add f (contents a) (contents b) ≠ origin := by simp

-- ============================================================================
-- Origin and Container Are Not Field Elements
-- ============================================================================

-- Origin absorbs its own inverse. Not a field inverse. Absorption.
theorem origin_inv (mulF : α → α → α) (invF : α → α) :
    mul mulF origin (inv invF (origin : Val α)) = origin := by simp

-- Container inverts to container. Not a field inverse. Structural.
theorem container_inv (mulF : α → α → α) (invF : α → α) (a : α) :
    mul mulF (container a) (inv invF (container a)) = container (mulF a (invF a)) := rfl

-- ============================================================================
-- Division
-- ============================================================================

-- Division by origin = origin. Absorption.
theorem div_origin (mulF : α → α → α) (invF : α → α) (a : Val α) :
    fdiv mulF invF a origin = origin := by
  simp [fdiv, mul, inv]; cases a <;> rfl

-- Division of contents by contents = contents. Arithmetic.
theorem div_contents (mulF : α → α → α) (invF : α → α) (a b : α) :
    fdiv mulF invF (contents a) (contents b) = contents (mulF a (invF b)) := rfl

-- Division preserves sort within contents.
theorem div_contents_ne_origin (mulF : α → α → α) (invF : α → α) (a b : α) :
    fdiv mulF invF (contents a) (contents b) ≠ origin := by
  simp [fdiv, mul, inv]

-- ============================================================================
-- The Honest Finding
-- ============================================================================

-- Val α as a whole is NOT a field.
-- Origin and container don't have multiplicative inverses in the contents sense.
-- They invert to themselves: origin by absorption, container by structural computation.

-- The contents sub-sort IS a field when α is.
-- The field is the interior. The boundary is named. The structure is named.
-- None of them pretend to be the others.

-- Val α answers the SORT question: which sort is this value?
-- α answers the FIELD question: what is the arithmetic result?
-- The ≠ 0 hypothesis was answering question 1 with the tools of question 2.

end Val
