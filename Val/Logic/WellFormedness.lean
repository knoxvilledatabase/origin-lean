/-
Released under MIT license.
-/
import Val.Field

/-!
# Val Logic: Well-Formedness — The Core Pattern

The logic equivalent of Singularity.lean. Core patterns that every
logic file uses.

A well-formed sentence is contents. A sentence not in the object
language — self-referential, outside the formal system, reaching for
its own ground — was never in the counting domain. Origin is not
where it ended up. Origin is where it always was.

The key result: the no-contents-fixed-point theorem. If a function f
has no fixed point on α, then no contents value is a fixed point of
valMap f on Val α. Origin satisfies the equation vacuously — but
origin is not in the counting domain. The equation has no counting-domain
answer. This is the structural reason paradoxes of self-reference can't
have truth values.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Bool Instance for Logic
-- ============================================================================

instance boolValArith : ValArith Bool where
  mulF := Bool.and
  addF := Bool.or
  negF := Bool.not
  invF := Bool.not

-- ============================================================================
-- The No-Contents-Fixed-Point Theorem
-- ============================================================================

-- If f has no fixed point on α (∀ a, f a ≠ a), then:
--   - No contents value satisfies valMap f v = v
--   - No container value satisfies valMap f v = v
--   - Origin satisfies it vacuously (valMap f origin = origin)
--   - But origin is not in the counting domain
--
-- This is the general theorem behind the Liar paradox, Russell's paradox,
-- and every self-reference paradox. The question asks for a counting-domain
-- value that is its own f-image. No such value exists. Origin satisfies
-- the equation, but origin is the ground — not a value.
--
-- The formal system can't hold its own ground. The shepherd can't hold
-- the ground he stands on. Not because the ground is too heavy.
-- Because holding is something that happens ON the ground.

/-- If f has no fixed point on α, the only fixed point of valMap f on Val α
    is origin — which is not in the counting domain. -/
theorem no_contents_fixed_point
    (f : α → α) (hf : ∀ a : α, f a ≠ a)
    (v : Val α) (hv : valMap f v = v) : v = origin := by
  cases v with
  | origin => rfl
  | container a => simp [valMap] at hv; exact absurd hv (hf a)
  | contents a => simp [valMap] at hv; exact absurd hv (hf a)

/-- Corollary for neg: if negF has no fixed point, neg has no
    counting-domain fixed point. -/
theorem no_neg_fixed_point [ValArith α]
    (hf : ∀ a : α, ValArith.negF a ≠ a)
    (v : Val α) (hv : neg v = v) : v = origin := by
  cases v with
  | origin => rfl
  | container a => simp [neg] at hv; exact absurd hv (hf a)
  | contents a => simp [neg] at hv; exact absurd hv (hf a)

/-- Origin always satisfies valMap f origin = origin. Vacuously.
    This is not a resolution. It's the ground being the ground. -/
theorem origin_always_fixed (f : α → α) :
    valMap f (origin : Val α) = origin := rfl

-- ============================================================================
-- Classical Logic in Contents
-- ============================================================================

-- Classical logic lives entirely in contents. All operations compute.
-- Origin never enters. The counting domain is clean.

example : mul (contents true) (contents true) = (contents true : Val Bool) := rfl
example : mul (contents true) (contents false) = (contents false : Val Bool) := rfl
example : add (contents true) (contents false) = (contents true : Val Bool) := rfl
example : add (contents false) (contents false) = (contents false : Val Bool) := rfl
example : neg (contents true) = (contents false : Val Bool) := rfl
example : neg (contents false) = (contents true : Val Bool) := rfl

-- Contents is closed under all operations. If both inputs are contents,
-- the output is contents. No operation on contents produces origin.
-- The counting domain is self-contained. Origin is outside it.

-- ============================================================================
-- Compound Well-Formedness
-- ============================================================================

-- If any component of a compound sentence is not in the well-formed domain,
-- the compound is not in the well-formed domain. Not because the operation
-- "failed" — because the input was never in the counting domain.

/-- Conjunction with non-well-formed component: not in counting domain. -/
theorem conj_origin_left (q : Val Bool) : mul origin q = (origin : Val Bool) := by
  cases q <;> rfl

/-- Disjunction with non-well-formed component: not in counting domain. -/
theorem disj_origin_left (q : Val Bool) : add origin q = (origin : Val Bool) := by
  cases q <;> rfl

-- These follow from mul_origin_left and add_origin_left in Arith.lean.
-- Named here for the logic context: well-formedness propagates through
-- compound sentences because the components must all be in the counting
-- domain for the compound to be.

-- ============================================================================
-- Well-Formedness Hypothesis Dissolution
-- ============================================================================

-- Every standard logic theorem about evaluation carries h : φ is well-formed.
-- In Val: the sort carries well-formedness. The hypothesis doesn't exist.
-- This is the same mechanism as ≠ 0 in mathematics and existence in physics.
--
-- The sort doesn't prevent non-well-formed sentences from existing as a
-- concept. It prevents them from entering the counting domain. A sentence
-- outside the object language was never a contents value. Evaluation of
-- origin gives origin — not because evaluation "failed," but because
-- origin is the ground evaluation stands on.

end Val
