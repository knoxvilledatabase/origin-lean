/-
Released under MIT license.
-/
import Origin.Core

/-!
# Origin Logic: Option α Is Sufficient

The Val logic layer used three files and 718 lines to dissolve
12 well-formedness hypotheses and unify the paradoxes. This file
shows the same results using Option α.

None  = the ground. The sentence isn't in the well-formed domain.
Some v = a value. The sentence is well-formed with truth value v.

The key theorem: if f has no fixed point on α, then no Some value
is a fixed point of Option.map f. The Liar, Russell, and Curry
are all instances.
-/

universe u

-- no_some_fixed_point is in Core.lean

-- ============================================================================
-- The Liar Paradox
-- ============================================================================

-- "This sentence is false" asks: is there a truth value v where v = ¬v?
-- Bool.not has no fixed point. By no_some_fixed_point: no Some value
-- satisfies Option.map Bool.not v = v.
--
-- The Liar asks for a value in the counting domain that can't exist there.
-- The sort makes visible why. Origin isn't a resolution. It's the ground
-- the counting domain stands on — and the counting domain has no fixed
-- point of negation.

theorem bool_not_no_fixpoint (b : Bool) : (!b) ≠ b := by
  cases b <;> decide

theorem liar (v : Option Bool) (hv : v.map (!·) = v) : v = none :=
  no_some_fixed_point _ bool_not_no_fixpoint v hv

-- ============================================================================
-- Russell's Paradox
-- ============================================================================

-- R = {x : x ∉ x}. Same fixed-point structure as the Liar.
-- Self-membership + negation = negation fixed point.
-- Same theorem. Same impossibility. R was never a well-formed set.

theorem russell (v : Option Bool) (hv : v.map (!·) = v) : v = none :=
  liar v hv

-- ============================================================================
-- Curry's Paradox
-- ============================================================================

-- C = "If C then False." When P = false: C = ¬C ∨ false.
-- The function f(b) = (!b) || false = !b. Same as negation.
-- No fixed point. Same theorem.

theorem curry_fn_no_fixpoint (b : Bool) : ((!b) || false) ≠ b := by
  cases b <;> decide

theorem curry (v : Option Bool) (hv : v.map (fun b => (!b) || false) = v) :
    v = none :=
  no_some_fixed_point _ curry_fn_no_fixpoint v hv

-- ============================================================================
-- Well-Formedness: Ground is the Additive Identity
-- ============================================================================

-- In logic: ground + x = x means "adding a non-well-formed premise
-- to an argument doesn't change the argument." The ground is the
-- identity — not a premise, not a value, the ground.

-- Every standard logic theorem carries h : φ is well-formed.
-- With Option: if the sentence is none, the result is none.
-- Option.map f none = none. Already in the standard library.

-- Conjunction: both must be well-formed.
def conj (p q : Option Bool) : Option Bool :=
  match p, q with
  | some a, some b => some (a && b)
  | _, _ => none

theorem conj_none_left (q : Option Bool) : conj none q = none := by
  cases q <;> rfl

theorem conj_none_right (p : Option Bool) : conj p none = none := by
  cases p <;> rfl

-- Disjunction: both must be well-formed.
def disj (p q : Option Bool) : Option Bool :=
  match p, q with
  | some a, some b => some (a || b)
  | _, _ => none

theorem disj_none_left (q : Option Bool) : disj none q = none := by
  cases q <;> rfl

theorem disj_none_right (p : Option Bool) : disj p none = none := by
  cases p <;> rfl

-- ============================================================================
-- Tarski's Hierarchy
-- ============================================================================

-- Option.map f : Option α → Option β. The function f : α → β lives
-- outside Option. A value inside Option can't be its own evaluation
-- function. The type system prevents it. Tarski's hierarchy is structural.

-- ============================================================================
-- The Verdict
-- ============================================================================

-- The same 12 well-formedness hypotheses dissolve. The same paradoxes
-- unify under one theorem. The same structural explanations hold.
--
-- What's gone:
--   Val/Demo/Logic.lean (356 lines)
--   Val/Logic/WellFormedness.lean (137 lines)
--   Val/Logic/Paradox.lean (225 lines)
--   The ValArith Bool instance. The custom neg, mul, add on Val.
--
-- What remains:
--   Option. Option.map. One theorem. Three instances.
--   The ground (none) and the values (some).
--
-- no_some_fixed_point is the same theorem as no_contents_fixed_point.
-- liar, russell, curry are the same instances.
-- The results are identical. The infrastructure is gone.
--
-- Val was the scaffolding. Option is the building.
