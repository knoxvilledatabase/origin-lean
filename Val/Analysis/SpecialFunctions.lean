/-
Released under MIT license.
-/
import Val.Analysis.Core

/-!
# Val α: Special Functions

exp, log, trig, pow, gamma, beta.
Contents in, contents out. The sort is known. The value is α's problem.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Exponential
-- ============================================================================

/-- exp(x) for contents is contents. exp never produces origin. -/
theorem exp_contents (expF : α → α) (x : α) :
    ∃ r, (contents (expF x) : Val α) = contents r := ⟨expF x, rfl⟩

theorem exp_ne_origin (expF : α → α) (x : α) :
    (contents (expF x) : Val α) ≠ origin := by intro h; cases h

/-- exp(a + b) = exp(a) · exp(b) within contents. -/
theorem exp_add [Add α] [Mul α] (expF : α → α)
    (h : ∀ a b : α, expF (a + b) = expF a * expF b) (a b : α) :
    (contents (expF (a + b)) : Val α) = contents (expF a * expF b) := by rw [h]

/-- exp(zero) = one within contents. -/
theorem exp_zero [Zero α] (expF : α → α) (one : α) (h : expF 0 = one) :
    (contents (expF 0) : Val α) = contents one := by
  show contents (expF 0) = contents one; rw [h]

-- ============================================================================
-- Logarithm
-- ============================================================================

/-- log(x) for contents is contents. No x ≠ 0 at sort level. -/
theorem log_contents (logF : α → α) (x : α) :
    ∃ r, (contents (logF x) : Val α) = contents r := ⟨logF x, rfl⟩

theorem log_ne_origin (logF : α → α) (x : α) :
    (contents (logF x) : Val α) ≠ origin := by intro h; cases h

/-- log(a · b) = log(a) + log(b) within contents. No a ≠ 0, b ≠ 0 at sort level. -/
theorem log_mul [Mul α] [Add α] (logF : α → α)
    (h : ∀ a b : α, logF (a * b) = logF a + logF b) (a b : α) :
    (contents (logF (a * b)) : Val α) = contents (logF a + logF b) := by rw [h]

/-- log(exp(x)) = x within contents. -/
theorem log_exp (logF expF : α → α) (h : ∀ x, logF (expF x) = x) (x : α) :
    (contents (logF (expF x)) : Val α) = contents x := by
  show contents (logF (expF x)) = contents x; rw [h]

/-- Derivative of log: 1/x. Contents ÷ contents = contents. No x ≠ 0 at sort level. -/
theorem log_deriv [Mul α] (invF : α → α) (one : α) (x : α) :
    ∃ r, (contents (one * invF x) : Val α) = contents r :=
  ⟨one * invF x, rfl⟩

-- ============================================================================
-- Trigonometric Functions
-- ============================================================================

/-- sin(x) for contents is contents. -/
theorem sin_contents (sinF : α → α) (x : α) :
    ∃ r, (contents (sinF x) : Val α) = contents r := ⟨sinF x, rfl⟩

/-- cos(x) for contents is contents. -/
theorem cos_contents (cosF : α → α) (x : α) :
    ∃ r, (contents (cosF x) : Val α) = contents r := ⟨cosF x, rfl⟩

/-- tan(x) = sin(x)/cos(x). Contents / contents = contents. No cos(x) ≠ 0 at sort level. -/
theorem tan_contents [Mul α] (sinF cosF : α → α) (invF : α → α) (x : α) :
    ∃ r, (contents (sinF x * invF (cosF x)) : Val α) = contents r :=
  ⟨sinF x * invF (cosF x), rfl⟩

/-- sin²(x) + cos²(x) = one within contents. -/
theorem pythagorean [Mul α] [Add α] (sinF cosF : α → α) (one : α)
    (h : ∀ x : α, sinF x * sinF x + cosF x * cosF x = one) (x : α) :
    (contents (sinF x * sinF x + cosF x * cosF x) : Val α) = contents one := by rw [h]

-- ============================================================================
-- Power Functions
-- ============================================================================

/-- x^n for contents is contents. -/
theorem pow_contents (powF : α → α → α) (x n : α) :
    ∃ r, (contents (powF x n) : Val α) = contents r := ⟨powF x n, rfl⟩

/-- x^n is never origin for contents inputs. -/
theorem pow_ne_origin (powF : α → α → α) (x n : α) :
    (contents (powF x n) : Val α) ≠ origin := by intro h; cases h

/-- x^(a+b) = x^a · x^b within contents. -/
theorem pow_add_exp [Mul α] [Add α] (powF : α → α → α)
    (h : ∀ x a b : α, powF x (a + b) = powF x a * powF x b) (x a b : α) :
    (contents (powF x (a + b)) : Val α) = contents (powF x a * powF x b) := by rw [h]

-- ============================================================================
-- Gamma and Beta Functions
-- ============================================================================

/-- Gamma(x) for contents is contents. -/
theorem gamma_contents (gammaF : α → α) (x : α) :
    ∃ r, (contents (gammaF x) : Val α) = contents r := ⟨gammaF x, rfl⟩

/-- Gamma(x) is never origin for contents input. -/
theorem gamma_ne_origin (gammaF : α → α) (x : α) :
    (contents (gammaF x) : Val α) ≠ origin := by intro h; cases h

/-- Beta(a,b) = Gamma(a)·Gamma(b)/Gamma(a+b). Contents throughout.
    No Gamma(a+b) ≠ 0 at sort level. -/
theorem beta_contents [Mul α] [Add α] (gammaF : α → α) (invF : α → α) (a b : α) :
    ∃ r, (contents (gammaF a * gammaF b * invF (gammaF (a + b))) : Val α) = contents r :=
  ⟨gammaF a * gammaF b * invF (gammaF (a + b)), rfl⟩

-- ============================================================================
-- Universal
-- ============================================================================

/-- Any special function applied to contents gives contents. Universal. -/
theorem any_special_fn_contents (f : α → α) (x : α) :
    (contents (f x) : Val α) ≠ origin := by intro h; cases h

/-- Any special function composition stays in contents. -/
theorem special_fn_comp_contents (f g : α → α) (x : α) :
    ∃ r, (contents (f (g x)) : Val α) = contents r := ⟨f (g x), rfl⟩

end Val
