/-
Released under MIT license.
-/
import Val.Analysis.Core
import Val.FunctionalAnalysis

/-!
# Val α: Normed Spaces

Normed groups, normed rings, normed fields, operator norms, Banach spaces.
Contents in, contents out. The sort is structural. No ≠ 0 at sort level.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Normed Group: The Base Layer
-- ============================================================================

/-- A norm function on α. Maps α values to α. -/
def valNormGroup (normF : α → α) : Val α → Val α
  | origin => origin
  | container a => container (normF a)
  | contents a => contents (normF a)

/-- ‖0‖ = 0 within contents. -/
theorem valNormGroup_zero [Zero α] (normF : α → α) (h : normF 0 = 0) :
    valNormGroup normF (contents (0 : α)) = contents 0 := by
  show contents (normF 0) = contents 0; rw [h]

/-- Triangle inequality: ‖x + y‖ ≤ ‖x‖ + ‖y‖ within contents. -/
theorem valNormGroup_triangle [Add α] [LE α] (normF : α → α)
    (h : ∀ a b : α, normF (a + b) ≤ normF a + normF b) (a b : α) :
    normF (a + b) ≤ normF a + normF b :=
  h a b

/-- ‖-x‖ = ‖x‖ within contents. -/
theorem valNormGroup_neg [Neg α] (normF : α → α)
    (h : ∀ a : α, normF (-a) = normF a) (a : α) :
    valNormGroup normF (neg Neg.neg (contents a)) = valNormGroup normF (contents a) := by
  show contents (normF (-a)) = contents (normF a); rw [h]

/-- Norm of contents is never origin. -/
theorem valNormGroup_ne_origin (normF : α → α) (a : α) :
    valNormGroup normF (contents a) ≠ origin := by intro h; cases h

-- ============================================================================
-- Normed Ring: Submultiplicativity
-- ============================================================================

/-- ‖x * y‖ ≤ ‖x‖ * ‖y‖ within contents. -/
theorem norm_mul_submul [Mul α] [LE α] (normF : α → α)
    (h : ∀ a b : α, normF (a * b) ≤ normF a * normF b) (a b : α) :
    normF (a * b) ≤ normF a * normF b :=
  h a b

/-- ‖1‖ = 1 within contents. -/
theorem norm_one_contents (one : α) (normF : α → α) (h : normF one = one) :
    valNormGroup normF (contents one) = contents one := by
  show contents (normF one) = contents one; rw [h]

-- ============================================================================
-- Normed Field: ‖x * y‖ = ‖x‖ * ‖y‖
-- ============================================================================

/-- In a normed field, the norm is multiplicative. -/
theorem norm_mul_eq [Mul α] (normF : α → α)
    (h : ∀ a b : α, normF (a * b) = normF a * normF b) (a b : α) :
    valNormGroup normF (contents (a * b)) =
    contents (normF a * normF b) := by
  show contents (normF (a * b)) = contents (normF a * normF b); rw [h]

/-- ‖invF(x)‖ = invF(‖x‖) within contents. No ‖x‖ ≠ 0 hypothesis. -/
theorem norm_inv_contents (normF invF : α → α)
    (h : ∀ a : α, normF (invF a) = invF (normF a)) (a : α) :
    valNormGroup normF (contents (invF a)) = contents (invF (normF a)) := by
  show contents (normF (invF a)) = contents (invF (normF a)); rw [h]

-- ============================================================================
-- Operator Norm
-- ============================================================================

/-- Operator norm: T applied to contents gives contents. No ‖x‖ ≠ 0 sort hypothesis. -/
theorem op_norm_ne_origin (normF : α → α) (T : α → α) (a : α) :
    valNormGroup normF (opApply T (contents a)) ≠ origin := by
  intro h; cases h

/-- Operator applied to contents: contents out. -/
theorem op_norm_is_contents (normF : α → α) (T : α → α) (a : α) :
    ∃ r, valNormGroup normF (opApply T (contents a)) = contents r :=
  ⟨normF (T a), rfl⟩

/-- Bounded operator: ‖T(x)‖ ≤ opNorm · ‖x‖. -/
theorem bounded_op_contents [Mul α] [LE α] (normF : α → α) (T : α → α) (opNorm : α)
    (h : ∀ a, normF (T a) ≤ opNorm * normF a) (a : α) :
    normF (T a) ≤ opNorm * normF a :=
  h a

-- ============================================================================
-- Completeness: Banach Spaces
-- ============================================================================

/-- A Banach space is a complete normed space. Cauchy sequences in contents
    converge to contents limits. -/
theorem banach_completeness
    (conv : (Nat → α) → α → Prop)
    (isCauchy : (Nat → α) → Prop)
    (complete : ∀ s : Nat → α, isCauchy s → ∃ L, conv s L)
    (s : Nat → α) (hs : isCauchy s) :
    ∃ L, liftConv conv (fun n => contents (s n)) (contents L) := by
  obtain ⟨L, hL⟩ := complete s hs
  exact ⟨L, s, fun _ => rfl, hL⟩

-- ============================================================================
-- Equivalence of Norms
-- ============================================================================

/-- Two norms are equivalent: C₁‖x‖₁ ≤ ‖x‖₂ ≤ C₂‖x‖₁. -/
theorem norm_equiv_contents [LE α] [Mul α]
    (norm1 norm2 : α → α) (C1 C2 : α)
    (h1 : ∀ a, C1 * norm1 a ≤ norm2 a)
    (h2 : ∀ a, norm2 a ≤ C2 * norm1 a) (a : α) :
    C1 * norm1 a ≤ norm2 a ∧ norm2 a ≤ C2 * norm1 a :=
  ⟨h1 a, h2 a⟩

-- ============================================================================
-- Seminorms
-- ============================================================================

/-- A seminorm: ‖x‖ = 0 doesn't imply x = 0.
    contents(0) is contents. Origin is origin. No confusion. -/
theorem seminorm_zero_is_contents [Zero α] (seminormF : α → α) (h : seminormF 0 = 0) :
    valNormGroup seminormF (contents (0 : α)) = contents 0 := by
  show contents (seminormF 0) = contents 0; rw [h]

end Val
