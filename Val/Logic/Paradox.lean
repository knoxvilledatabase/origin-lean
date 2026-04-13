/-
Released under MIT license.
-/
import Val.Logic.WellFormedness

/-!
# Val Logic: Paradox — Contents Can't Hold Its Own Ground

Every paradox of self-reference has the same structure: a formal system
asks a question whose answer would require stepping outside the counting
domain the system is built on. The question is well-formed (contents).
The answer can't be contents. The formal system is trying to hold the
ground it stands on.

The no-contents-fixed-point theorem from WellFormedness.lean is the
general tool. This file applies it to specific paradoxes and shows
Tarski's hierarchy as the structural consequence.

## The Honest Boundary

Val names why the paradoxes arise. It does not resolve them.

The Liar paradox in full generality, Gödel's incompleteness, the halting
problem, and the full machinery of proof theory remain as they are. What
Val contributes is structural: the sort system makes certain confusions
visible as type-level impossibilities rather than semantic paradoxes.

This is narrower than what math and physics contributed. In math, 9,682
hypotheses dissolved. In physics, 86 existence hypotheses dissolved.
In logic, 12 well-formedness hypotheses dissolve, and the paradoxes get
structural explanations — but the paradoxes themselves are consequences
of the counting domain being finite, not of a missing sort.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Part 1: The Liar Paradox — Instance of No-Contents-Fixed-Point
-- ============================================================================

-- "This sentence is false" asks: is there a truth value v where v = ¬v?
-- Bool.not has no fixed point: !true = false ≠ true, !false = true ≠ false.
-- By no_contents_fixed_point: no contents value satisfies neg v = v.
--
-- The Liar doesn't "evaluate to origin." The Liar asks for a contents
-- answer that can't exist. The sort system makes visible why — the
-- contents domain has no fixed point of negation. A truth value that
-- equals its own negation would need to step outside the counting domain.
-- You can't do that from inside contents.

/-- Bool.not has no fixed point. -/
theorem bool_not_no_fixpoint (b : Bool) : !b ≠ b := by cases b <;> decide

/-- The Liar: no contents truth value equals its own negation. -/
theorem liar_no_contents_solution (v : Val Bool) (hv : neg v = v) :
    v = origin :=
  no_neg_fixed_point (fun b => by cases b <;> decide) v hv

-- What this says: the equation S = ¬S, applied to Val Bool, has exactly
-- one inhabitant — origin. But origin is not True, not False, not a truth
-- value at all. It is the ground truth values stand on.
--
-- The Liar sentence is asking: "Can I hold the ground I stand on?"
-- The answer is not "no, you get origin instead." The answer is that
-- holding is something that happens on the ground. The ground is the
-- precondition for holding, not a thing that can be held.

-- ============================================================================
-- Part 2: Russell's Paradox — Self-Membership as Ground-Reaching
-- ============================================================================

-- R = {x : x ∉ x}. Is R ∈ R?
--
-- If R ∈ R, then by definition R ∉ R. Contradiction.
-- If R ∉ R, then by definition R ∈ R. Contradiction.
--
-- In Val: the membership function for R is "check if x is NOT in x."
-- Applying this to R itself requires R to evaluate its own membership
-- status — to step outside itself and judge itself from the ground
-- the sets stand on. That's not a computation that fails. It's a
-- question that was never in the counting domain.
--
-- Formally: R's self-membership is a fixed-point question.
-- membership(R, R) = ¬membership(R, R). Same structure as the Liar.

/-- Russell's paradox has the same fixed-point structure as the Liar.
    Self-membership + negation = no contents fixed point. -/
theorem russell_no_contents_solution (v : Val Bool) (hv : neg v = v) :
    v = origin :=
  liar_no_contents_solution v hv

-- Russell's paradox and the Liar are the same theorem.
-- Both ask: can a contents value be its own negation?
-- No. The only value satisfying v = ¬v is origin — the ground.
-- R was never a well-formed set. The sentence was never well-formed.
-- Not because self-reference is prohibited (that's the patch).
-- Because the question requires holding the ground.

-- ============================================================================
-- Part 3: Curry's Paradox — Conditional Self-Reference
-- ============================================================================

-- C = "If C then P." If C is true, then P (by C's definition).
-- So C → P. But we assumed C, so P. For ANY P. Inconsistency.
--
-- In Val: C = C → P is C = ¬C ∨ P (material implication).
-- This is: add (neg C) P = C.
-- When P = contents false (the dangerous case — proving false):
--   add (neg C) (contents false) = C
--   For C = contents true:  add (contents false) (contents false) = contents false ≠ contents true ✗
--   For C = contents false: add (contents true) (contents false) = contents true ≠ contents false ✗
-- No contents solution when P is false.
--
-- Curry's paradox can't prove false in contents. The question
-- "if this sentence is true, then false" has no contents answer.

/-- Curry's paradox: C = ¬C ∨ False has no contents solution. -/
theorem curry_no_contents_solution (v : Val Bool)
    (hv : add (neg v) (contents false) = v) :
    v = origin := by
  cases v with
  | origin => rfl
  | container b => exact absurd hv (by cases b <;> decide)
  | contents b => exact absurd hv (by cases b <;> decide)

-- ============================================================================
-- Part 4: Tarski's Hierarchy — Structural Consequence
-- ============================================================================

-- Why do we need Truth₀, Truth₁, Truth₂...?
--
-- Not as a patch. As a consequence.
--
-- valMap f : Val α → Val β. The function f : α → β lives outside Val.
-- It operates on the contents of Val values. It cannot be a Val value
-- itself — it's a different type. A Val α value that tried to be its
-- own evaluation function would need to be both contents (the thing
-- being evaluated) and the function doing the evaluating (which lives
-- outside contents).
--
-- That's the fish trying to be the ocean. The shepherd trying to hold
-- the ground. The formal system trying to contain its own precondition.
--
-- Tarski's hierarchy makes this explicit at each level:
-- - Level 0 sentences are evaluated by the Level 1 truth predicate
-- - Level 1 sentences are evaluated by the Level 2 truth predicate
-- - No level evaluates itself
--
-- In Val: valMap is the evaluation. The function lives one level up.
-- This is structural, not conventional. The type system enforces it.

/-- Evaluation preserves sort: if the input is in the counting domain,
    the output is in the counting domain. The function adds no origin. -/
theorem eval_preserves_sort {β : Type u} (f : α → β) (a : α) :
    valMap f (contents a) = contents (f a) := rfl

/-- Evaluation maps the ground to the ground. Not as a computation
    that "returns origin." As the ground being the ground at the
    output level, the same way it's the ground at the input level. -/
theorem eval_ground_is_ground {β : Type u} (f : α → β) :
    valMap f (origin : Val α) = (origin : Val β) := rfl

-- The hierarchy is the type-level fact that f : α → β is not Val α.
-- A sentence can't evaluate itself because evaluation lives outside
-- the sentence. This isn't a restriction imposed on the system.
-- It's what evaluation means.

-- ============================================================================
-- Part 5: Gödel and the Halting Problem — Contents Questions About the Ground
-- ============================================================================

-- Gödel's incompleteness: the sentence G = "G is not provable in S"
-- is well-formed (contents). Its truth value is well-defined (contents —
-- it's true in the standard model). But its provability within S
-- would require S to evaluate its own consistency — to step outside
-- the counting domain and judge it from the ground.
--
-- The sentence exists. Its truth exists. What doesn't exist (in the
-- system) is a proof of the sentence. Not because the system hit a
-- wall. Because proving it would require the system to hold its own
-- ground.
--
-- The halting problem: the question "does program P halt on input P?"
-- is well-formed (contents). But if the answer existed as a contents
-- value, it would generate a contradiction within contents (the
-- standard diagonalization). The question isn't about origin. It's
-- about the counting domain trying to contain a fact about its own
-- ground.
--
-- Val doesn't resolve either of these. They are about the structural
-- limitations of formal systems — what contents can prove about itself.
-- Val makes the reason visible: the system is trying to hold its own
-- ground. The no-contents-fixed-point theorem is the general form.
-- Gödel and Turing are specific instances at the proof-theoretic
-- and computational levels.

-- ============================================================================
-- Part 6: The Verdict
-- ============================================================================

-- WHAT DOES VAL CONTRIBUTE TO THE LOGIC OF SELF-REFERENCE?
--
-- Not resolution. Structural explanation.
--
-- Every paradox of self-reference asks: can a contents value hold
-- its own ground? The no-contents-fixed-point theorem answers: no.
-- Not because origin blocks it. Because the counting domain has no
-- value with that property. The question was never a contents question.
--
-- The specific instances:
--   Liar:    S = ¬S has no contents solution (no fixed point of negation)
--   Russell: R ∈ R ↔ R ∉ R is the same equation (negation fixed point)
--   Curry:   C = (C → False) has no contents solution
--   Tarski:  evaluation lives outside the evaluated (type structure)
--   Gödel:   provability of consistency requires holding the ground
--   Halting:  decidability of halting requires holding the ground
--
-- Each is a case of the formal system trying to hold the ground it
-- stands on. The sort system makes this visible. The shepherd always
-- knew he couldn't hold the ground. Now there's a type that says why.

end Val
