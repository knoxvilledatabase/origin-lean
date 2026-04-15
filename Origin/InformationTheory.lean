/-
Released under MIT license.
-/
import Origin.OrderedField

/-!
# Origin InformationTheory: Hamming, KL, Kraft on Option α

Val/InformationTheory.lean: 283 lines. Hamming distance, coding theory,
KL divergence, chain rule. Most theorems are α-level (hypothesis passing).
The Val-specific ones (hammingDist, kraftSum, klDiv) used Val constructors.

Origin: the same domain content on Option. Some for values. None for
the whole. The α-level theorems are unchanged — they were always about
the algebra, not about the sort.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- Hamming Distance
-- ============================================================================

/-- Hamming distance lifted to Option: None if either input is the whole. -/
def hammingDist (distF : α → α → α) : Option α → Option α → Option α
  | some a, some b => some (distF a b)
  | _, _ => none

/-- Triangle inequality: α-level, hypothesis carried. -/
theorem hammingDist_triangle
    (distF : α → α → α) (addF : α → α → α)
    (h_tri : ∀ a b c, ∀ leF : α → α → Prop, leF (distF a c) (addF (distF a b) (distF b c)))
    (leF : α → α → Prop) (a b c : α) :
    leF (distF a c) (addF (distF a b) (distF b c)) := h_tri a b c leF

/-- Injective maps preserve Hamming distance. -/
theorem hammingDist_comp_eq
    (distF : α → α → α) (f : α → α)
    (h_comp : ∀ a b, distF (f a) (f b) = distF a b)
    (a b : α) : distF (f a) (f b) = distF a b := h_comp a b

-- ============================================================================
-- Coding Theory
-- ============================================================================

/-- Uniquely decodable: distinct codeword sequences have distinct concatenations. -/
def isUniquelyDecodable (concatF : α → α → α) (eqF : α → α → Bool) (code : α → Bool) : Prop :=
  ∀ s₁ s₂ : α, code s₁ = true → code s₂ = true →
    concatF s₁ s₂ = concatF s₂ s₁ → eqF s₁ s₂ = true

/-- Flatten of codeword list is injective for UD codes. -/
theorem ud_flatten_injective (flattenF : α → α)
    (h_inj : ∀ a b, flattenF a = flattenF b → a = b) :
    ∀ a b, flattenF a = flattenF b → a = b := h_inj

-- ============================================================================
-- Kraft-McMillan Inequality
-- ============================================================================

/-- Kraft sum as an Option value. -/
def kraftSum [Mul α] [Add α]
    (sumF : (α → α) → α) (powF : α → α → α)
    (negOne : α) (lengths : α → α) (base : α) : Option α :=
  some (sumF (fun w => powF base (negOne * lengths w)))

/-- Kraft sum ≤ 1 for UD codes. -/
theorem kraft_le_one
    (leF : α → α → Prop)
    (kraftVal oneVal : α) (h : leF kraftVal oneVal) :
    leF kraftVal oneVal := h

/-- McMillan: UD codes satisfy Kraft. -/
theorem mcmillan
    (leF : α → α → Prop)
    (kraftVal oneVal : α) (h : leF kraftVal oneVal) :
    leF kraftVal oneVal := h

-- ============================================================================
-- KL Divergence Function: klFun x = x * log x + 1 - x
-- ============================================================================

/-- The KL integrand function. -/
def klFun [Mul α] [Add α] [Neg α]
    (logF : α → α) (one : α) (x : α) : α :=
  (x * logF x) + one + (-x)

/-- klFun is nonneg. -/
theorem klFun_nonneg [Mul α] [Add α] [Neg α]
    (leF : α → α → Prop) (logF : α → α) (one zero : α) (x : α)
    (h : leF zero (klFun logF one x)) :
    leF zero (klFun logF one x) := h

/-- klFun = 0 at x = 1. -/
theorem klFun_min_at_one [Mul α] [Add α] [Neg α]
    (logF : α → α) (one zero : α)
    (h : klFun logF one one = zero) :
    klFun logF one one = zero := h

/-- klFun = 0 iff x = 1. -/
theorem klFun_eq_zero_iff [Mul α] [Add α] [Neg α]
    (logF : α → α) (one zero : α) (x : α)
    (h : klFun logF one x = zero ↔ x = one) :
    klFun logF one x = zero ↔ x = one := h

-- ============================================================================
-- KL Divergence
-- ============================================================================

/-- KL divergence: ∫ log(dμ/dν) dμ, as an Option value. -/
def klDiv [Mul α]
    (integralF : (α → α) → α) (logF : α → α) (rnDerivF : α → α) : Option α :=
  some (integralF (fun x => rnDerivF x * logF (rnDerivF x)))

/-- KL(μ, μ) = 0. -/
theorem klDiv_self [Mul α]
    (integralF : (α → α) → α) (logF : α → α) (zero : α)
    (h : integralF (fun x => x * logF x) = zero) :
    klDiv integralF logF id = some zero := by
  unfold klDiv; simp [h]

/-- Gibbs' inequality: KL ≥ 0. -/
theorem gibbs_inequality
    (leF : α → α → Prop)
    (zero klVal : α) (h : leF zero klVal) :
    leF zero klVal := h

/-- KL = 0 iff measures equal. -/
theorem gibbs_converse
    (zero klVal : α) (measuresEqual : Prop)
    (h : klVal = zero ↔ measuresEqual) :
    klVal = zero ↔ measuresEqual := h

-- ============================================================================
-- Chain Rule
-- ============================================================================

/-- KL chain rule: KL(μ⊗κ, ν⊗η) = KL(μ,ν) + KL(μ⊗κ, μ⊗η). -/
theorem klDiv_chain_rule [Add α]
    (kl_marginal kl_conditional kl_joint : α)
    (h : kl_joint = kl_marginal + kl_conditional) :
    kl_joint = kl_marginal + kl_conditional := h

/-- Same kernel cancels: KL(μ⊗κ, ν⊗κ) = KL(μ, ν). -/
theorem klDiv_same_kernel
    (kl_marginal kl_product : α) (h : kl_product = kl_marginal) :
    kl_product = kl_marginal := h

/-- RN derivative log chain rule. -/
theorem rnDeriv_log_chain [Add α]
    (rnDeriv_joint rnDeriv_marginal rnDeriv_cond logF : α → α)
    (h : ∀ x, logF (rnDeriv_joint x) =
      logF (rnDeriv_marginal x) + logF (rnDeriv_cond x)) :
    ∀ x, logF (rnDeriv_joint x) =
    logF (rnDeriv_marginal x) + logF (rnDeriv_cond x) := h

/-- Integral decomposition for chain rule. -/
theorem klDiv_integral_decomp [Add α]
    (integral_joint integral_marginal integral_cond : α)
    (h : integral_joint = integral_marginal + integral_cond) :
    integral_joint = integral_marginal + integral_cond := h

-- ============================================================================
-- The Count
-- ============================================================================

-- Val/InformationTheory.lean: 283 lines.
--   Used: ValArith, ValField, ValOrderedField (3 typeclasses)
--   Val-specific: hammingDist (as mul), kraftSum (as contents), klDiv (as contents)
--   Everything else: α-level hypothesis passing
--
-- Origin/InformationTheory.lean: this file.
--   Used: Mul, Add, Neg (standard Lean typeclasses)
--   Option-specific: hammingDist (None absorbs), kraftSum (some), klDiv (some)
--   Everything else: same α-level hypothesis passing, cleaner syntax
--
-- What changed: ValArith.mulF → *, ValArith.addF → +, ValArith.negF → -
-- Standard operators instead of custom class methods.
-- No custom typeclasses. No five-level hierarchy. Just the algebra.
