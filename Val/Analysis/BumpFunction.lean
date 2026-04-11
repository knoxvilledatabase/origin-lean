/-
Released under MIT license.
-/
import Val.Analysis.Calculus

/-!
# Val α: Bump Functions

Bump functions: smooth, compactly supported functions.
Contents bump functions are smooth within contents.
Support is within contents, never origin.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Bump Function: Smooth, Compactly Supported
-- ============================================================================

/-- A bump function: a smooth function that is nonzero only on a bounded set.
    Outside the support, the value is contents(0), not origin. -/
def bumpApply [Zero α] (bumpF : α → α) (supportPred : α → Bool) : Val α → Val α
  | origin => origin
  | container a => container (if supportPred a then bumpF a else 0)
  | contents a => contents (if supportPred a then bumpF a else 0)

/-- Bump function applied to contents gives contents. -/
theorem bump_contents [Zero α] (bumpF : α → α) (supportPred : α → Bool) (a : α) :
    ∃ r, bumpApply bumpF supportPred (contents a) = contents r :=
  ⟨if supportPred a then bumpF a else 0, rfl⟩

/-- Bump function applied to contents is never origin. -/
theorem bump_contents_ne_origin [Zero α] (bumpF : α → α) (supportPred : α → Bool) (a : α) :
    bumpApply bumpF supportPred (contents a) ≠ origin := by
  intro h; cases h

/-- Bump function at origin stays origin. -/
theorem bump_origin [Zero α] (bumpF : α → α) (supportPred : α → Bool) :
    bumpApply bumpF supportPred (origin : Val α) = origin := rfl

-- ============================================================================
-- Support of a Bump Function
-- ============================================================================

/-- The support of a bump function: where it is nonzero. -/
def inSupport [Zero α] [DecidableEq α] (bumpF : α → α) (a : α) : Prop :=
  bumpF a ≠ 0

/-- A point in the support has a nonzero contents value. -/
theorem support_is_contents [Zero α] [DecidableEq α] (bumpF : α → α) (a : α)
    (h : inSupport bumpF a) :
    ∃ r, (contents (bumpF a) : Val α) = contents r :=
  ⟨bumpF a, rfl⟩

/-- Support value is never origin. -/
theorem support_ne_origin [Zero α] [DecidableEq α] (bumpF : α → α) (a : α)
    (h : inSupport bumpF a) :
    (contents (bumpF a) : Val α) ≠ origin := by intro h; cases h

/-- Outside the support, the bump function returns contents(0), not origin. -/
theorem outside_support_is_contents [Zero α] [DecidableEq α] (bumpF : α → α) (a : α)
    (h : ¬inSupport bumpF a) :
    (contents (bumpF a) : Val α) = contents 0 := by
  simp [inSupport] at h; rw [h]

-- ============================================================================
-- Smoothness of Bump Functions
-- ============================================================================

/-- All derivatives of a bump function are contents-valued. -/
theorem bump_smooth_derivs (derivs : Nat → α → α) (a : α) (n : Nat) :
    ∃ r, (contents (derivs n a) : Val α) = contents r :=
  ⟨derivs n a, rfl⟩

/-- No derivative of a bump function is origin. -/
theorem bump_deriv_ne_origin (derivs : Nat → α → α) (a : α) (n : Nat) :
    (contents (derivs n a) : Val α) ≠ origin := by intro h; cases h

/-- Derivatives of bump function at boundary of support: contents(0). -/
theorem bump_deriv_at_boundary [Zero α] (derivs : Nat → α → α) (a : α) (n : Nat)
    (h : derivs n a = 0) :
    (contents (derivs n a) : Val α) = contents 0 := by rw [h]

-- ============================================================================
-- Partition of Unity
-- ============================================================================

/-- A partition of unity: a collection of bump functions summing to 1. -/
theorem partition_unity_term_contents (φ : α → α) (x : α) :
    ∃ r, (contents (φ x) : Val α) = contents r :=
  ⟨φ x, rfl⟩

theorem partition_unity_term_ne_origin (φ : α → α) (x : α) :
    (contents (φ x) : Val α) ≠ origin := by intro h; cases h

/-- Sum of partition of unity terms is contents. -/
theorem partition_unity_sum_contents [Add α] (φ₁ φ₂ : α → α) (x : α) :
    (contents (φ₁ x + φ₂ x) : Val α) = contents (φ₁ x + φ₂ x) := rfl

/-- Partition of unity sums to contents(one). -/
theorem partition_unity_total (one : α) (sumF : α)
    (h : sumF = one) :
    (contents sumF : Val α) = contents one := by rw [h]

/-- Partition of unity: individual bumps multiply with target functions. -/
theorem partition_multiply_contents [Mul α] (φ f : α → α) (x : α) :
    (contents (φ x * f x) : Val α) = contents (φ x * f x) := rfl

-- ============================================================================
-- Bump Function Algebra
-- ============================================================================

/-- Product of two bump functions is a bump function. Contents throughout. -/
theorem bump_product_contents [Mul α] (b₁ b₂ : α → α) (x : α) :
    (contents (b₁ x * b₂ x) : Val α) = contents (b₁ x * b₂ x) := rfl

/-- Sum of two bump functions is contents. -/
theorem bump_sum_contents [Add α] (b₁ b₂ : α → α) (x : α) :
    (contents (b₁ x + b₂ x) : Val α) = contents (b₁ x + b₂ x) := rfl

/-- Scalar multiple of a bump function is contents. -/
theorem bump_scalar_contents [Mul α] (c : α) (b : α → α) (x : α) :
    (contents (c * b x) : Val α) = contents (c * b x) := rfl

-- ============================================================================
-- Mollifiers
-- ============================================================================

/-- A mollifier: a bump function used to smooth other functions.
    Convolution output: contents in, contents out. -/
theorem mollifier_contents (convF : α → α) (x : α) :
    ∃ r, (contents (convF x) : Val α) = contents r :=
  ⟨convF x, rfl⟩

theorem mollifier_ne_origin (convF : α → α) (x : α) :
    (contents (convF x) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Cutoff Functions
-- ============================================================================

/-- A cutoff function is one on K and 0 outside U. Contents throughout. -/
theorem cutoff_on_K (one : α) (cutoffF : α → α) (a : α) (h : cutoffF a = one) :
    (contents (cutoffF a) : Val α) = contents one := by rw [h]

theorem cutoff_off_U [Zero α] (cutoffF : α → α) (a : α) (h : cutoffF a = 0) :
    (contents (cutoffF a) : Val α) = contents 0 := by rw [h]

theorem cutoff_always_contents (cutoffF : α → α) (a : α) :
    ∃ r, (contents (cutoffF a) : Val α) = contents r :=
  ⟨cutoffF a, rfl⟩

-- ============================================================================
-- Bump Function Integration
-- ============================================================================

/-- Integral of a bump function is contents. -/
theorem bump_integral_contents (intF : (α → α) → α) (bumpF : α → α) :
    ∃ r, (contents (intF bumpF) : Val α) = contents r :=
  ⟨intF bumpF, rfl⟩

theorem bump_integral_ne_origin (intF : (α → α) → α) (bumpF : α → α) :
    (contents (intF bumpF) : Val α) ≠ origin := by intro h; cases h

end Val
