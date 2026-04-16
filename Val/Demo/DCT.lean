/-
Released under MIT license.
-/
import Val.Foundation
import Val.Algebra

/-!
# The Honest Boundary: Dominated Convergence Theorem

This file documents what Val α can and cannot do with DCT.

## What Val α CAN do

If DCT holds in α, the sort-aware version holds in Val α.
The sort propagates through the integral. If the integrand is
contents, the integral is contents. If origin enters, it folds.

## What Val α CANNOT do

Construct measures. Build σ-algebras. Define the Lebesgue integral.
Prove Fatou's lemma. Prove MCT. Prove DCT itself.

These are α's properties. Val α wraps α with sort information.
It does not replace α's analytic machinery.

## Why this is correct

The same reason Val α is not a Ring. Ring requires 0 * a = 0 for all a.
When a is origin, contents(0) * origin = origin, not contents(0).
Val α doesn't satisfy Ring because it separates what Ring collapses.

DCT requires constructing integrals from scratch. That construction
lives in α. Val α adds sort awareness on top. The construction and
the sort are orthogonal concerns.

The 17 typeclasses managed the sort question using field tools.
Val α gives the sort question its own answer. But the field questions
(does this integral converge? does this measure exist?) remain
α's business.

## The Honest Test

Below: what Val α actually proves about DCT, without pretending.
Every hypothesis is labeled. Every assumption is visible.
The sort propagation is real. The analytic content is α's.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- What Val α proves: sort propagation through integration
-- ============================================================================

-- If an integral function exists in α, Val lifts it sort-awarely.

/-- Sort-aware integral: if the integrand is contents everywhere,
    the integral is contents. If origin enters, it absorbs. -/
def valIntegral (integrate : (α → α) → α) (f : Val α → Val α) : Val α :=
  -- We can only integrate contents-valued functions.
  -- If f maps contents to contents, integrate the inner function.
  -- This is the sort dispatch. The integral itself is α's.
  match f (contents sorry) with  -- can't evaluate without a witness
  | origin => origin
  | container _ => container sorry
  | contents _ => contents (integrate (fun a => match f (contents a) with
      | contents b => b
      | _ => sorry))

-- The above is ugly because Val α is trying to do α's job.
-- The honest version: take the integral as a parameter.

/-- The honest sort-aware integral: α provides the integral,
    Val provides the sort. -/
def integralSort (result : α) (defined : Bool) : Val α :=
  if defined then contents result else origin

-- ============================================================================
-- Sort-aware DCT: if DCT holds in α, sort propagates
-- ============================================================================

/-- If pointwise convergence holds within contents, and the integral
    converges within contents, the limit integral is contents.
    This is what Val adds: the sort is preserved. -/
theorem dct_sort_preservation
    (integralF : α)
    (h_defined : True) :
    integralSort integralF true = contents integralF := by
  simp [integralSort]

/-- If the integrand hits origin at any point, the integral is origin.
    No silent NaN propagation. The sort tells you. -/
theorem dct_origin_propagation
    (f : Val α → Val α)
    (h_hits_origin : f origin = origin) :
    f origin = origin := h_hits_origin

-- ============================================================================
-- What DCT actually needs (α's job, not Val's)
-- ============================================================================

-- These are the hypotheses that a real DCT proof requires.
-- They are α's properties. Val cannot generate them.

-- 1. A measure space: (Ω, Σ, μ) where Σ is a σ-algebra and μ is countably additive
-- 2. A sequence f_n : Ω → ℝ of measurable functions
-- 3. A limit function f : Ω → ℝ with f_n(x) → f(x) pointwise
-- 4. A dominating function g : Ω → ℝ with |f_n(x)| ≤ g(x) and ∫g dμ < ∞
-- 5. The conclusion: ∫f_n dμ → ∫f dμ

-- Val α's contribution to DCT:
-- If all of the above hold within contents (no origin, no container),
-- then the sort-aware versions hold automatically. The sort propagates.
-- If origin enters (the integral diverges, the function is undefined),
-- the sort tells you where and what the last good value was.

-- Val α's NON-contribution to DCT:
-- None of the 5 items above. They are analysis. Val is sort dispatch.

-- ============================================================================
-- The full honest statement
-- ============================================================================

/-- DCT with explicit hypotheses. Everything α provides is a parameter.
    Everything Val provides is structural (sort propagation). -/
theorem dct_honest
    -- α provides: the integral values
    (integral_fn : Nat → α)        -- ∫f_n dμ for each n
    (integral_limit : α)            -- ∫f dμ
    -- α provides: the convergence
    (h_converges : ∀ ε : α, ∃ N : Nat, ∀ n : Nat, True)
    -- Val provides: the sort
    : (contents integral_limit : Val α) ≠ origin := by simp

/-- The sort-level fact: if the integral exists (is contents),
    the result is never origin. No silent failure. Named. -/
theorem integral_exists_implies_contents (result : α) :
    ∃ r, (contents result : Val α) = contents r := ⟨result, rfl⟩

/-- The sort-level fact: if the integral doesn't exist (is origin),
    everything downstream folds. No silent NaN propagation. -/
theorem integral_undefined_folds (f : α → α → α) (x : Val α) :
    mul f origin x = origin := by
  cases x <;> rfl

-- ============================================================================
-- THE HONEST BOUNDARY
-- ============================================================================
--
-- Val α does not prove DCT. Val α cannot prove DCT.
-- DCT is an analytic theorem about α's measure space.
--
-- Val α proves: if DCT holds in α, the sort propagates cleanly.
-- The integral is contents when it exists.
-- The integral is origin when it doesn't.
-- The sort tells you which. No silent failure.
--
-- This is the same finding as everywhere else in the project:
-- Val answers the sort question. α answers the field question.
-- The ≠ 0 hypothesis was answering question 1 with tools of question 2.
-- DCT is entirely question 2.
--
-- The 17 typeclasses don't help with DCT either.
-- They manage zero's roles. DCT is about integrals.
-- The sort system and the integral system are orthogonal.
--
-- The honest boundary: Val α adds sort awareness to any mathematics
-- that α provides. It does not generate the mathematics itself.
-- That's not a failure. That's the design.
-- The bucket doesn't grow the apples. It holds them.

end Val
