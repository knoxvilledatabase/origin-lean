/-
Released under MIT license.
-/
import Val.PolyRing
import Val.RingTheory.Core

/-!
# Val α: RingTheory — Polynomial Rings

Polynomial degree, leading coefficient, division, multivariate monomials,
power series, Hahn series, and polynomial substitution.

Key dissolution: leading coefficient ≠ 0 guards in polynomial division.
In Val α, contents leading coefficients are never origin. Structural.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Leading Coefficient
-- ============================================================================

/-- Leading coefficient of a polynomial (last element). -/
def leadCoeff : List (Val α) → Val α
  | [] => origin
  | [a] => a
  | _ :: rest => leadCoeff rest

theorem leadCoeff_single (a : Val α) : leadCoeff [a] = a := rfl

theorem leadCoeff_contents_val (a : α) : leadCoeff [contents a] = contents a := rfl

/-- Leading coefficient of contents polynomial is never origin. -/
theorem leadCoeff_contents_ne_origin (a : α) :
    leadCoeff [contents a] ≠ (origin : Val α) := by
  intro h; cases h

-- ============================================================================
-- Polynomial Division: The ≠ 0 Dissolution
-- ============================================================================

/-- Division step: a / b within contents. No leading coeff ≠ 0 guard. -/
theorem poly_div_step (mulF : α → α → α) (invF : α → α) (a b : α) :
    mul mulF (contents a) (inv invF (contents b)) = contents (mulF a (invF b)) := rfl

/-- Division step never produces origin. -/
theorem poly_div_ne_origin (mulF : α → α → α) (invF : α → α) (a b : α) :
    mul mulF (contents a) (inv invF (contents b)) ≠ origin := by
  simp

-- ============================================================================
-- Multivariate Monomials
-- ============================================================================

/-- Multivariate monomial: coefficient × product of variable values. -/
def mvMonomial (mulF : α → α → α) (coeff : Val α) (vars : List (Val α)) : Val α :=
  vars.foldl (mul mulF) coeff

theorem mvMonomial_origin (mulF : α → α → α) (vars : List (Val α)) :
    mvMonomial mulF origin vars = origin := by
  induction vars with
  | nil => rfl
  | cons v rest ih =>
    show List.foldl (mul mulF) (mul mulF origin v) rest = origin
    have : mul mulF origin v = (origin : Val α) := by cases v <;> rfl
    rw [this]; exact ih

theorem mvMonomial_contents_nil (mulF : α → α → α) (a : α) :
    mvMonomial mulF (contents a) [] = contents a := rfl

/-- Contents coefficient with one contents variable stays in contents. -/
theorem mvMonomial_contents_one (mulF : α → α → α) (a b : α) :
    mvMonomial mulF (contents a) [contents b] = contents (mulF a b) := rfl

/-- Multivariate monomial with contents coefficient and variables is never origin. -/
theorem mvMonomial_contents_ne_origin (mulF : α → α → α) (a b : α) :
    mvMonomial mulF (contents a) [contents b] ≠ (origin : Val α) := by
  intro h; cases h

-- ============================================================================
-- Power Series: Formal Sums
-- ============================================================================

/-- Partial sum of a power series: first n+1 terms evaluated at x. -/
def powerSeriesPartial (addF mulF : α → α → α) :
    (Nat → Val α) → Nat → Val α → Val α
  | coeffs, 0, _ => coeffs 0
  | coeffs, n + 1, x => add addF (powerSeriesPartial addF mulF coeffs n x) (mul mulF x (coeffs (n + 1)))

theorem powerSeries_zero_term (addF mulF : α → α → α)
    (coeffs : Nat → Val α) (x : Val α) :
    powerSeriesPartial addF mulF coeffs 0 x = coeffs 0 := rfl

/-- Contents coefficients base case: first term is contents. -/
theorem powerSeries_contents_base (addF mulF : α → α → α) (f : Nat → α) :
    powerSeriesPartial addF mulF (fun n => contents (f n)) 0 (contents (f 0)) =
    contents (f 0) := rfl

-- ============================================================================
-- Hahn Series
-- ============================================================================

/-- Hahn series coefficient access: contents coefficient or origin. -/
def hahnCoeff (f : Nat → Val α) (n : Nat) : Val α := f n

theorem hahnCoeff_contents (f : Nat → α) (n : Nat) :
    hahnCoeff (fun i => contents (f i)) n = contents (f n) := rfl

/-- Origin coefficient stays origin. -/
theorem hahnCoeff_origin (f : Nat → Val α) (n : Nat) (h : f n = origin) :
    hahnCoeff f n = origin := h

-- ============================================================================
-- Polynomial Substitution
-- ============================================================================

/-- Substitution: replace variable with a Val α expression. -/
def substitute (addF mulF : α → α → α) (zero : α)
    (poly : List (Val α)) (expr : Val α) : Val α :=
  polyEval addF mulF zero poly expr

theorem substitute_at_origin (addF mulF : α → α → α) (zero : α)
    (poly : List (Val α)) :
    substitute addF mulF zero poly origin = polyEval addF mulF zero poly origin := rfl

theorem substitute_contents_linear (addF mulF : α → α → α) (zero : α) (a₀ a₁ v : α) :
    substitute addF mulF zero [contents a₀, contents a₁] (contents v) =
    contents (addF a₀ (mulF v a₁)) := rfl

end Val
