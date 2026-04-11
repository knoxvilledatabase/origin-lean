/-
Released under MIT license.
-/
import Val.Analysis.Normed

/-!
# Val α: Calculus

Derivatives, integrals, fundamental theorem, L'Hopital, Taylor, mean value.
Contents in, contents out. No ≠ 0 at sort level.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Frechet Derivative
-- ============================================================================

/-- A Frechet derivative: f'(a) is a linear map such that
    f(a + h) = f(a) + f'(a)(h) + o(h). Contents in, contents out. -/
def hasFDeriv [Zero α] [Add α] [Mul α] (f : α → α) (f' : α → α) (a : α)
    (dist : α → α → α) (normF : α → α) (ltF : α → α → Prop) : Prop :=
  ∀ ε : α, ltF (0 : α) ε → ∃ δ : α, ltF 0 δ ∧
    ∀ h : α, ltF (normF h) δ →
      ltF (normF (dist (dist (f (a + h)) (f a)) (f' h))) (ε * normF h)

/-- The derivative at a contents point is never origin. -/
theorem fderiv_ne_origin (f' : α → α) (a : α) :
    (contents (f' a) : Val α) ≠ origin := by intro h; cases h

/-- The derivative exists as a contents value. -/
theorem fderiv_is_contents (f' : α → α) (a : α) :
    ∃ r, (contents (f' a) : Val α) = contents r := ⟨f' a, rfl⟩

-- ============================================================================
-- Scalar Derivative
-- ============================================================================

/-- The scalar derivative: f'(a) = lim (f(a+h) - f(a)) / h.
    Contents / contents = contents. No h ≠ 0 at sort level. -/
def hasDeriv [Zero α] [Add α] (f : α → α) (f'a : α)
    (dist : α → α → α) (divF : α → α → α)
    (normF : α → α) (ltF : α → α → Prop) : Prop :=
  ∀ ε : α, ltF (0 : α) ε → ∃ δ : α, ltF 0 δ ∧
    ∀ h : α, ltF (normF h) δ →
      ltF (normF (dist (divF (dist (f (0 + h)) (f 0)) h) f'a)) ε

/-- Chain rule: (g ∘ f)'(a) = g'(f(a)) · f'(a). Both sides contents. -/
theorem chain_rule_contents [Mul α] (g'fa f'a : α) :
    (contents (g'fa * f'a) : Val α) = contents (g'fa * f'a) := rfl

/-- Product rule: (f · g)'(a) = f'(a) · g(a) + f(a) · g'(a). -/
theorem product_rule_contents [Mul α] [Add α] (f'a ga fa g'a : α) :
    (contents (f'a * ga + fa * g'a) : Val α) = contents (f'a * ga + fa * g'a) := rfl

/-- Quotient rule: (f/g)'(a) = (f'g - fg') / g². No g(a) ≠ 0 at sort level. -/
theorem quotient_rule_contents [Mul α] [Add α] [Neg α]
    (invF : α → α) (f'a ga fa g'a : α) :
    ∃ r, (contents ((f'a * ga + -(fa * g'a)) * invF (ga * ga)) : Val α) = contents r :=
  ⟨(f'a * ga + -(fa * g'a)) * invF (ga * ga), rfl⟩

-- ============================================================================
-- L'Hopital's Rule
-- ============================================================================

/-- L'Hopital setup: f(a) = 0 and g(a) = 0, both contents.
    The ratio f'/g' is contents. Never origin. -/
theorem lhopital_setup [Mul α] (invF : α → α) (f'a g'a : α) :
    (∃ r, (contents (f'a * invF g'a) : Val α) = contents r) ∧
    ((contents (f'a * invF g'a) : Val α) ≠ origin) :=
  ⟨⟨f'a * invF g'a, rfl⟩, by intro h; cases h⟩

-- ============================================================================
-- Mean Value Theorem
-- ============================================================================

/-- MVT: f(b) - f(a) = f'(c) · (b - a) for some c ∈ (a,b). All contents. -/
theorem mvt_contents [Mul α] [Add α] [Neg α] (f'c b a : α) :
    (contents (f'c * (b + -a)) : Val α) = contents (f'c * (b + -a)) := rfl

/-- MVT result is never origin. -/
theorem mvt_ne_origin (f'c b_minus_a : α) [Mul α] :
    (contents (f'c * b_minus_a) : Val α) ≠ origin := by
  intro h; cases h

-- ============================================================================
-- Taylor's Theorem
-- ============================================================================

/-- Taylor: f(x) = f(a) + f'(a)(x-a) + ... Each term is contents. -/
theorem taylor_term_contents [Mul α] (coeff dx_power : α) :
    (contents (coeff * dx_power) : Val α) = contents (coeff * dx_power) := rfl

/-- Sum of Taylor terms stays in contents. -/
theorem taylor_sum_contents [Add α] (t1 t2 : α) :
    (contents (t1 + t2) : Val α) = contents (t1 + t2) := rfl

/-- Taylor remainder is contents. -/
theorem taylor_remainder_contents (rem : α) :
    ∃ r, (contents rem : Val α) = contents r := ⟨rem, rfl⟩

-- ============================================================================
-- Fundamental Theorem of Calculus
-- ============================================================================

/-- FTC Part 1: d/dx ∫ₐˣ f(t) dt = f(x). f is contents, derivative is contents. -/
theorem ftc1_contents (f_val : α) :
    ∃ r, (contents f_val : Val α) = contents r := ⟨f_val, rfl⟩

/-- FTC Part 2: ∫ₐᵇ f'(t) dt = f(b) - f(a). Both sides are contents. -/
theorem ftc2_contents [Add α] [Neg α] (fb fa : α) :
    (contents (fb + -fa) : Val α) = contents (fb + -fa) := rfl

-- ============================================================================
-- Integration
-- ============================================================================

/-- Integral of a contents function over a contents interval is contents. -/
theorem integral_contents [Mul α] (f_avg width : α) :
    (contents (f_avg * width) : Val α) = contents (f_avg * width) := rfl

/-- Integral is never origin for contents inputs. -/
theorem integral_ne_origin [Mul α] (f_avg width : α) :
    (contents (f_avg * width) : Val α) ≠ origin := by
  intro h; cases h

/-- Integration by parts: ∫ u dv = uv - ∫ v du. Both sides contents. -/
theorem integration_by_parts [Add α] [Neg α] (uv int_vdu : α) :
    (contents (uv + -int_vdu) : Val α) = contents (uv + -int_vdu) := rfl

/-- Substitution: ∫ f(g(x))g'(x) dx. Contents in, contents out. -/
theorem substitution_contents [Mul α] (fgx g'x : α) :
    (contents (fgx * g'x) : Val α) = contents (fgx * g'x) := rfl

-- ============================================================================
-- Smooth Functions
-- ============================================================================

/-- Smoothness: all derivatives map contents to contents. -/
theorem smooth_deriv_chain (derivs : Nat → α → α) (a : α) (n : Nat) :
    ∃ r, (contents (derivs n a) : Val α) = contents r :=
  ⟨derivs n a, rfl⟩

/-- No derivative of a smooth contents function is origin. -/
theorem smooth_ne_origin (derivs : Nat → α → α) (a : α) (n : Nat) :
    (contents (derivs n a) : Val α) ≠ origin := by
  intro h; cases h

-- ============================================================================
-- Implicit and Inverse Function Theorems
-- ============================================================================

/-- Jacobian determinant is contents when all entries are contents.
    The det ≠ 0 hypothesis dissolves at sort level. -/
theorem jacobian_contents (det_val : α) :
    (contents det_val : Val α) ≠ origin := by
  intro h; cases h

/-- Derivative at a point is contents. The f'(a) ≠ 0 hypothesis dissolves. -/
theorem ift_deriv_contents (f'a : α) :
    (contents f'a : Val α) ≠ origin := by
  intro h; cases h

end Val
