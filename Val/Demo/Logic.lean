/-
Released under MIT license.
-/
import Val.Field

/-!
# Demo: Logic — Does Origin Handle Well-Formedness Boundaries?

The test: does Val's origin/contents distinction dissolve well-formedness
hypotheses in formal logic the way it dissolved existence hypotheses in
physics and ≠ 0 hypotheses in mathematics?

In standard formal logic, every theorem about truth evaluation carries
h : φ is well-formed. Every theorem about predication carries
h : P is a predicate in the language. Every meta-theorem about truth
carries h : truth predicate is for THIS level.

In Val: if the sentence isn't well-formed, it's origin. If it is, it's
contents. The sort carries well-formedness. The hypothesis doesn't exist.

The Liar paradox: no contents value is a fixed point of negation.
The question "what is the truth value of 'this sentence is false'?"
is asking for a contents answer that can't exist. The sort system
makes visible why — the question requires a truth value to evaluate
its own ground. That can't happen from inside contents.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Bool Instance for Logic
-- ============================================================================

instance : ValArith Bool where
  mulF := Bool.and
  addF := Bool.or
  negF := Bool.not
  invF := Bool.not

-- ============================================================================
-- Part 1: Truth Evaluation — Well-Formedness Dissolved
-- ============================================================================

-- A sentence in a formal system:
--   origin    = not a well-formed sentence. Not "a sentence that failed" —
--               a sentence that was never in the counting domain. The ground
--               the well-formed sentences stand on.
--   contents v = well-formed sentence with truth value v
--   container v = sentence was well-formed, last known truth value preserved

/-- Evaluate a sentence. If not well-formed, the truth value is origin.
    Standard: requires h : φ is well-formed. Val: sort dispatch. -/
def evalSentence (sentence : Val Bool) : Val Bool := sentence

/-- Non-well-formed sentence: no truth value. -/
theorem eval_not_wf : evalSentence (origin : Val Bool) = origin := rfl

/-- Well-formed sentence: truth value exists. -/
theorem eval_wf (v : Bool) : evalSentence (contents v) = contents v := rfl

-- ============================================================================
-- Part 2: Logical Connectives — Compound Well-Formedness
-- ============================================================================

-- In standard logic: φ ∧ ψ requires h₁ : φ wf, h₂ : ψ wf.
-- In Val: if either component is not in the well-formed domain,
-- the compound is not in the well-formed domain. One sort dispatch.

/-- Conjunction: both must be well-formed. -/
def conj (p q : Val Bool) : Val Bool := mul p q

/-- Left conjunct not well-formed: origin. -/
theorem conj_left_origin (q : Val Bool) :
    conj origin q = origin := by simp [conj]

/-- Right conjunct not well-formed: origin. -/
theorem conj_right_origin (p : Val Bool) :
    conj p origin = origin := by simp [conj]

/-- Both well-formed: computes. -/
theorem conj_contents (a b : Bool) :
    conj (contents a) (contents b) = contents (a && b) := rfl

/-- Disjunction: both must be well-formed. -/
def disj (p q : Val Bool) : Val Bool := add p q

/-- Left disjunct not well-formed: origin. -/
theorem disj_left_origin (q : Val Bool) :
    disj origin q = origin := by simp [disj]

/-- Right disjunct not well-formed: origin. -/
theorem disj_right_origin (p : Val Bool) :
    disj p origin = origin := by simp [disj]

/-- Negation: a sentence not in the well-formed domain stays there. -/
def negation (p : Val Bool) : Val Bool := neg p

/-- Negation of non-well-formed: origin. -/
theorem neg_not_wf : negation (origin : Val Bool) = origin := rfl

/-- Negation of well-formed: computes. -/
theorem neg_wf (v : Bool) : negation (contents v) = contents (!v) := rfl

-- ============================================================================
-- Part 3: The Liar Paradox — No Contents Fixed Point of Negation
-- ============================================================================

-- "This sentence is false" asks: is there a truth value v where v = ¬v?
-- The Liar is asking for a contents answer to a question that can't have one.
--
--   contents true:   neg (contents true) = contents false ≠ contents true  ✗
--   contents false:  neg (contents false) = contents true ≠ contents false  ✗
--
-- No contents value is a fixed point of negation. The question "what is
-- the truth value of a sentence that equals its own negation?" is asking
-- for something that doesn't exist in the contents domain.
--
-- Origin satisfies the equation vacuously (neg origin = origin), but that
-- isn't a resolution. Origin is not True. Origin is not False. Origin is
-- not a truth value at all. It's the ground the truth values stand on.
-- Saying "origin satisfies S = ¬S" is like saying "the ocean satisfies
-- the equation for fish" — technically the equation holds, but the ocean
-- isn't a fish.
--
-- The Liar doesn't "evaluate to origin." The Liar asks for a contents
-- answer that can't exist. The sort system makes visible why: a truth
-- value that equals its own negation would need to step outside the
-- counting domain. You can't do that from inside contents.

/-- Origin satisfies neg x = x vacuously. But origin is not a truth value. -/
theorem origin_neg_fixed : neg (origin : Val Bool) = origin := rfl

/-- True is not a fixed point. -/
theorem true_not_fixed : neg (contents true) ≠ (contents true : Val Bool) := by decide

/-- False is not a fixed point. -/
theorem false_not_fixed : neg (contents false) ≠ (contents false : Val Bool) := by decide

/-- No contents value is a fixed point of negation. -/
theorem contents_not_neg_fixed (v : Bool) :
    neg (contents v) ≠ (contents v : Val Bool) := by
  cases v <;> decide

-- What this proves about the Liar:
-- The Liar sentence is a well-formed question (contents) asking for
-- an answer that doesn't exist in the contents domain. Standard logic
-- prevents this by restricting self-reference (Tarski's hierarchy).
-- Val shows the structural reason the restriction is needed: the
-- contents domain has no fixed point of negation. The question is
-- asking about the ground the counting stands on. A formal system
-- can't evaluate its own ground from inside.

-- ============================================================================
-- Part 4: Predication — Subject-Predicate Well-Formedness
-- ============================================================================

-- "Socrates is mortal" requires:
--   h₁ : "Socrates" is a term in the language
--   h₂ : "is mortal" is a predicate in the language
-- In Val: if either is not in the language (origin), the predication
-- is not in the well-formed domain.

/-- Apply a predicate to a subject. -/
def predicate [ValArith α] (pred subject : Val α) : Val α :=
  mul pred subject

/-- Subject not in language: origin. -/
theorem pred_subject_origin [ValArith α] (pred : Val α) :
    predicate pred origin = origin := by simp [predicate]

/-- Predicate not in language: origin. -/
theorem pred_pred_origin [ValArith α] (subject : Val α) :
    predicate origin subject = origin := by simp [predicate]

-- ============================================================================
-- Part 5: Self-Reference — Reaching for the Ground
-- ============================================================================

-- Russell's paradox: R = {x : x ∉ x}. Is R ∈ R?
-- This question asks a set to evaluate its own membership — to step
-- outside itself and judge itself from the ground the sets stand on.
-- That's not a circular computation that "fails to complete." It's
-- a question that requires contents to evaluate its own origin.
-- The question was never a contents question.
--
-- In Val: a self-referential entity that must evaluate its own sort
-- to determine its own membership was never in the well-formed domain.
-- Origin is not where it ended up. Origin is where it always was.

/-- Applying any operation to origin gives origin. -/
theorem self_ref_origin [ValArith α] (membershipTest : α → α) :
    valMap membershipTest (origin : Val α) = origin := rfl

-- The structural fact: operations on origin give origin not because
-- the operation "fails" but because the input was never in the
-- counting domain. A self-referential set isn't a set that broke.
-- It was never a set. The sort carries this from the beginning.

-- ============================================================================
-- Part 6: Tarski's Hierarchy — Structural, Not Conventional
-- ============================================================================

-- Tarski's undefinability: no language can define its own truth predicate.
-- The standard response is a hierarchy: Truth₀ for level-0 sentences,
-- Truth₁ for level-1 sentences, etc. This looks like a patch.
--
-- In Val: truth evaluation is valMap. The evaluation function f : α → β
-- lives OUTSIDE Val. It cannot be a Val value. A Val value that tries
-- to be its own evaluation function would need to be both the contents
-- being evaluated and the ground doing the evaluating — both the fish
-- and the ocean simultaneously.
--
-- Tarski's hierarchy isn't a patch. It's a consequence of the type
-- structure. The reason you need a hierarchy is that a truth predicate
-- for a language can't be in that language — because that would require
-- a contents value to be its own origin. The hierarchy makes the
-- ground explicit at each level.

/-- Truth evaluation is valMap: the function lives outside Val. -/
theorem truth_is_valMap {β : Type u} (f : α → β) (s : Val α) :
    valMap f s = match s with
    | origin => origin
    | container a => container (f a)
    | contents a => contents (f a) := by
  cases s <;> rfl

-- The function f cannot be a Val α value. It's α → β, not Val α.
-- A sentence trying to be its own truth predicate would need the
-- evaluation function to also be an input to itself. The type system
-- prevents this — not as a restriction, but as a structural fact
-- about what it means to evaluate something from inside vs outside.

-- ============================================================================
-- Part 7: Modus Ponens — Inference with Well-Formedness
-- ============================================================================

-- From P and P → Q, conclude Q.
-- Standard: h₁ : P wf, h₂ : (P → Q) wf.
-- Val: if either premise is not in the well-formed domain, no conclusion.

/-- Modus ponens: if either premise is not well-formed, conclusion is origin. -/
def modusPonens [ValArith α] (p implication : Val α) : Val α :=
  mul p implication

/-- P not well-formed: no conclusion. -/
theorem mp_p_origin [ValArith α] (imp : Val α) :
    modusPonens origin imp = origin := by simp [modusPonens]

/-- Implication not well-formed: no conclusion. -/
theorem mp_imp_origin [ValArith α] (p : Val α) :
    modusPonens p origin = origin := by simp [modusPonens]

-- ============================================================================
-- Part 8: Quantification — Domain of Discourse
-- ============================================================================

-- "For all x, P(x)" requires every x in the domain to be well-formed.
-- If the domain includes entities not in the language (origin),
-- the universal quantification is not in the well-formed domain.

/-- Universal: if any element is not in the domain, the universal is origin. -/
def universal [ValArith α] (p₁ p₂ : Val α) : Val α :=
  mul p₁ p₂

/-- Element outside domain: universal origin. -/
theorem univ_element_origin [ValArith α] (p₂ : Val α) :
    universal origin p₂ = origin := by simp [universal]

/-- Existential: requires at least one well-formed witness.
    If no witness is in the well-formed domain, origin. -/
def existential [ValArith α] (p₁ p₂ : Val α) : Val α :=
  add p₁ p₂

/-- No well-formed witness: existential origin. -/
theorem exist_both_origin [ValArith α] :
    existential (origin : Val α) origin = origin := by
  simp [existential]

-- ============================================================================
-- Part 9: Comparison — Standard vs Val
-- ============================================================================

-- STANDARD APPROACH:
--
--   theorem eval (φ : Formula) (h : WellFormed φ) :
--       HasTruthValue (eval φ) := ...
--
--   theorem conjunction (φ ψ : Formula) (h₁ : WellFormed φ) (h₂ : WellFormed ψ) :
--       eval (φ ∧ ψ) = eval φ ∧ eval ψ := ...
--
--   theorem modus_ponens (P Q : Formula)
--       (h₁ : WellFormed P) (h₂ : WellFormed (P → Q)) :
--       eval (P → Q) ∧ eval P → eval Q := ...
--
--   theorem universal (P : Predicate) (h : ∀ x ∈ domain, WellFormed (P x)) :
--       eval (∀ x, P x) = ... := ...
--
-- Every theorem carries h : WellFormed. Multi-premise theorems thread multiple.

-- ============================================================================
-- Part 10: The Verdict
-- ============================================================================

-- DOES ORIGIN HANDLE WELL-FORMEDNESS BOUNDARIES IN LOGIC?
--
-- Yes. Every theorem in this file has zero well-formedness hypotheses.
-- The sort dispatch (origin/contents) handles well-formedness the same
-- way it handles existence in physics and ≠ 0 in mathematics.
--
-- The Liar paradox result: no contents value is a fixed point of negation.
-- The Liar asks for a contents answer that can't exist. Origin satisfies
-- the equation vacuously, but origin is not a truth value — it's the
-- ground the truth values stand on. The Liar doesn't "evaluate to origin."
-- The Liar is a well-formed question whose answer would require stepping
-- outside the counting domain. The sort system makes visible why no
-- contents answer exists.
--
-- Hypothesis count:
--
--   Theorem                         Standard              Val
--   ─────────────────────────────────────────────────────────────
--   eval_not_wf                     h : φ wf               0
--   conj_left_origin                h₁ : φ wf              0
--   conj_right_origin               h₂ : ψ wf              0
--   disj_left_origin                h₁ : φ wf              0
--   disj_right_origin               h₂ : ψ wf              0
--   neg_not_wf                      h : φ wf               0
--   contents_not_neg_fixed          0 (structural)         0
--   pred_subject_origin             h : subject in lang     0
--   pred_pred_origin                h : pred in lang        0
--   self_ref_origin                 n/a                    0
--   mp_p_origin                     h₁ : P wf              0
--   mp_imp_origin                   h₂ : (P→Q) wf          0
--   univ_element_origin             h : x in domain         0
--   exist_both_origin               h : ∃ witness wf        0
--   ─────────────────────────────────────────────────────────
--   Well-formedness hypotheses dissolved: 12
--
-- The Liar result is structural, not a dissolved hypothesis. It shows
-- why no contents resolution exists — not by providing an alternative
-- answer, but by making visible that the question requires evaluating
-- the ground from inside the counting domain.
--
-- The pattern holds across all three domains:
--   Mathematics: ≠ 0 hypotheses dissolved (sort carries zero-management)
--   Physics: existence hypotheses dissolved (sort carries existence)
--   Logic: well-formedness hypotheses dissolved (sort carries well-formedness)
--
-- Same constructor. Same sort dispatch. Same proof pattern.
-- Origin is never reached, approached, or hit. It is what the formal
-- system stands on. The sort makes that visible.

end Val
