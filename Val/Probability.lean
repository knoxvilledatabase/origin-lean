/-
Released under MIT license.
-/
import Val.MeasureTheory.Core
import Val.Analysis.Core

/-!
# Val α: Probability Theory

Probability measures are contents-valued measures where μ(Ω) = contents(1).
Random variables are contents-valued functions. Expectations are contents.
The sort propagates through conditioning, Bayes, and convergence.
-/

namespace Val

universe u
variable {α : Type u} {S : Type u}

-- ============================================================================
-- Random Variables
-- ============================================================================

/-- A contents random variable never hits origin. -/
theorem contentsRV_ne_origin (X : S → Val α) (hX : ∀ s, ∃ a, X s = contents a) (s : S) :
    X s ≠ origin := by
  obtain ⟨a, ha⟩ := hX s; rw [ha]; intro h; cases h

-- ============================================================================
-- Expectation
-- ============================================================================

/-- Expectation of a single outcome: f · P is contents. -/
theorem expectation_single (mulF : α → α → α) (f_val p_val : α) :
    mul mulF (contents f_val) (contents p_val) = contents (mulF f_val p_val) := rfl

/-- Expectation of two outcomes: f₁·P₁ + f₂·P₂ is contents. -/
theorem expectation_two (mulF addF : α → α → α) (f₁ p₁ f₂ p₂ : α) :
    add addF (mul mulF (contents f₁) (contents p₁))
             (mul mulF (contents f₂) (contents p₂)) =
    contents (addF (mulF f₁ p₁) (mulF f₂ p₂)) := rfl

/-- Expectation is never origin for contents inputs. -/
theorem expectation_ne_origin (mulF : α → α → α) (f_val p_val : α) :
    mul mulF (contents f_val) (contents p_val) ≠ origin := by simp

-- ============================================================================
-- Variance
-- ============================================================================

/-- Variance components: (X - μ) and (X - μ)² stay in contents. -/
theorem variance_components (mulF addF : α → α → α) (negF : α → α) (x μ : α) :
    (∃ r, add addF (contents x) (contents (negF μ)) = contents r) ∧
    (∃ r, mul mulF (contents (addF x (negF μ))) (contents (addF x (negF μ))) = contents r) :=
  ⟨⟨addF x (negF μ), rfl⟩, ⟨mulF (addF x (negF μ)) (addF x (negF μ)), rfl⟩⟩

-- ============================================================================
-- Conditional Probability
-- ============================================================================

/-- P(A|B) = P(A∩B) / P(B). Both numerator and denominator are contents.
    No P(B) ≠ 0 sort-level hypothesis needed. -/
theorem conditional_is_contents (mulF : α → α → α) (invF : α → α) (pAB pB : α) :
    ∃ r, mul mulF (contents pAB) (inv invF (contents pB)) = contents r :=
  ⟨mulF pAB (invF pB), rfl⟩

/-- Conditional probability is never origin. -/
theorem conditional_ne_origin (mulF : α → α → α) (invF : α → α) (pAB pB : α) :
    mul mulF (contents pAB) (inv invF (contents pB)) ≠ origin := by simp

-- ============================================================================
-- Bayes' Theorem
-- ============================================================================

/-- Bayes: P(A|B) = P(B|A) · P(A) / P(B). All components contents. -/
theorem bayes_is_contents (mulF : α → α → α) (invF : α → α) (pBA pA pB : α) :
    ∃ r, mul mulF (mul mulF (contents pBA) (contents pA))
                  (inv invF (contents pB)) = contents r :=
  ⟨mulF (mulF pBA pA) (invF pB), rfl⟩

/-- Bayes never hits origin from contents inputs. -/
theorem bayes_ne_origin (mulF : α → α → α) (invF : α → α) (pBA pA pB : α) :
    mul mulF (mul mulF (contents pBA) (contents pA))
             (inv invF (contents pB)) ≠ origin := by simp

-- ============================================================================
-- Independence
-- ============================================================================

/-- P(A∩B) = P(A)·P(B): independence is a contents-level property. -/
theorem independence_is_contents (mulF : α → α → α) (pA pB : α) :
    mul mulF (contents pA) (contents pB) = contents (mulF pA pB) := rfl

-- ============================================================================
-- Martingale
-- ============================================================================

/-- A martingale: E[Xₙ₊₁|Fₙ] = Xₙ. Both sides contents. -/
def isMartingale (X : Nat → α) (condExp : Nat → α → α) : Prop :=
  ∀ n, condExp n (X (n + 1)) = X n

/-- Martingale property lifts to Val α. -/
theorem martingale_lift (X : Nat → α) (condExp : Nat → α → α)
    (h : isMartingale X condExp) (n : Nat) :
    (contents (condExp n (X (n + 1))) : Val α) = contents (X n) := by
  show contents (condExp n (X (n + 1))) = contents (X n); rw [h]

-- ============================================================================
-- Stopping Time
-- ============================================================================

/-- Stopped value is contents, never origin. -/
theorem stopped_value_ne_origin (X : Nat → α) (T : Nat) :
    (contents (X T) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Convergence of Random Variables
-- ============================================================================

/-- Contents RVs converge to contents limits under liftConv. -/
theorem rv_convergence (conv : (Nat → α) → α → Prop) (X : Nat → α) (L : α)
    (h : conv X L) :
    liftConv conv (fun n => contents (X n)) (contents L) :=
  ⟨X, fun _ => rfl, h⟩

/-- The limit of a convergent sequence of contents RVs is contents. -/
theorem rv_limit_ne_origin (L : α) :
    (contents L : Val α) ≠ origin := by intro h; cases h

end Val
