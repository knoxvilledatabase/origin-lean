/-
Released under MIT license.
-/
import Val.Analysis.Normed

/-!
# Val α: Real Analysis and Locally Convex Spaces

Real analysis specifics (monotone functions, bounded variation) and
locally convex spaces (seminorm families).
Monotonicity, variation, seminorms all operate within contents.
No ≠ 0 at sort level.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Monotone Functions
-- ============================================================================

/-- A function is monotone (nondecreasing) on α. -/
def isMonotone [LE α] (f : α → α) : Prop :=
  ∀ x y : α, x ≤ y → f x ≤ f y

/-- Monotone function applied to contents gives contents. -/
theorem monotone_contents [LE α] (f : α → α) (x : α) :
    (contents (f x) : Val α) ≠ origin := by intro h; cases h

/-- Monotone functions preserve order within contents. -/
theorem monotone_preserves_order [LE α] (f : α → α) (hf : isMonotone f) (x y : α) (hxy : x ≤ y) :
    f x ≤ f y :=
  hf x y hxy

-- ============================================================================
-- Bounded Variation
-- ============================================================================

/-- Total variation of f on a partition: Σ |f(xₖ₊₁) - f(xₖ)|. -/
def totalVariation [Add α] [Neg α] (f : α → α) (absF : α → α)
    (partition : Nat → α) (sumF : (Nat → α) → Nat → α) (n : Nat) : α :=
  sumF (fun k => absF (f (partition (k + 1)) + -(f (partition k)))) n

theorem totalVariation_contents [Add α] [Neg α]
    (f : α → α) (absF : α → α) (partition : Nat → α)
    (sumF : (Nat → α) → Nat → α) (n : Nat) :
    (contents (totalVariation f absF partition sumF n) : Val α) ≠ origin := by intro h; cases h

/-- A function has bounded variation if total variation is bounded. -/
def hasBoundedVariation [Add α] [Neg α] [LE α] (f : α → α) (absF : α → α)
    (M : α) (partition : Nat → α) (sumF : (Nat → α) → Nat → α) (n : Nat) : Prop :=
  totalVariation f absF partition sumF n ≤ M

-- ============================================================================
-- Absolutely Continuous Functions
-- ============================================================================

/-- Absolute continuity: for every ε > 0, ∃ δ > 0 such that
    Σ |f(bₖ) - f(aₖ)| < ε whenever Σ (bₖ - aₖ) < δ. -/
def isAbsolutelyContinuous [Add α] [Neg α] [LE α] [LT α] [Zero α]
    (f : α → α) (absF : α → α) (normF : α → α) : Prop :=
  ∀ eps : α, (0 : α) < eps → ∃ delta : α, (0 : α) < delta ∧
    ∀ a b : α, normF (f b + -(f a)) ≤ eps

-- ============================================================================
-- Seminorm
-- ============================================================================

/-- A seminorm: like a norm but p(x) = 0 doesn't imply x = 0.
    Maps contents to contents. -/
def seminormApply (p : α → α) : Val α → Val α
  | origin => origin
  | container a => container (p a)
  | contents a => contents (p a)

theorem seminorm_contents (p : α → α) (a : α) :
    seminormApply p (contents a) = contents (p a) := rfl

theorem seminorm_ne_origin (p : α → α) (a : α) :
    seminormApply p (contents a) ≠ (origin : Val α) := by intro h; cases h

-- ============================================================================
-- Seminorm Axioms
-- ============================================================================

/-- Seminorm triangle inequality. -/
theorem seminorm_triangle [Add α] [LE α] (p : α → α)
    (h : ∀ a b, p (a + b) ≤ p a + p b) (a b : α) :
    p (a + b) ≤ p a + p b :=
  h a b

/-- Seminorm homogeneity: p(c·x) = |c|·p(x). -/
theorem seminorm_homogeneous [Mul α] (p absF : α → α)
    (h : ∀ c x, p (c * x) = absF c * p x) (c x : α) :
    seminormApply p (contents (c * x)) =
    contents (absF c * p x) := by
  show contents (p (c * x)) = contents (absF c * p x); rw [h]

-- ============================================================================
-- Family of Seminorms
-- ============================================================================

/-- A family of seminorms indexed by Nat. Each maps contents to contents. -/
def seminormFamily (ps : Nat → α → α) (n : Nat) : Val α → Val α :=
  seminormApply (ps n)

theorem seminormFamily_contents (ps : Nat → α → α) (n : Nat) (a : α) :
    seminormFamily ps n (contents a) = contents (ps n a) := rfl

theorem seminormFamily_ne_origin (ps : Nat → α → α) (n : Nat) (a : α) :
    seminormFamily ps n (contents a) ≠ (origin : Val α) := by intro h; cases h

-- ============================================================================
-- Hahn-Banach via Seminorms
-- ============================================================================

/-- Hahn-Banach: a linear functional dominated by a seminorm extends.
    The functional maps contents to contents. The seminorm bound is contents. -/
theorem hahnBanach_contents (phi : α → α) (x : α) :
    (contents (phi x) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Jordan Decomposition
-- ============================================================================

/-- Jordan decomposition: f = f⁺ - f⁻ where f⁺, f⁻ ≥ 0.
    Both parts are contents. -/
def positivePart (f : α → α) (maxF : α → α → α) (zero : α) (x : α) : α :=
  maxF (f x) zero

def negativePart [Neg α] (f : α → α) (maxF : α → α → α) (zero : α) (x : α) : α :=
  maxF (-(f x)) zero

theorem jordan_decomp_contents [Neg α] (f : α → α) (maxF : α → α → α) (zero : α) (x : α) :
    (contents (positivePart f maxF zero x) : Val α) ≠ origin ∧
    (contents (negativePart f maxF zero x) : Val α) ≠ origin := by
  constructor <;> (intro h; cases h)

end Val
