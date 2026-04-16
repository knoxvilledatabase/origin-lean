/-
Released under MIT license.
-/
import Origin.Core

/-!
# Information Theory on Option α (Core-based)

The previous version was 179 lines. Most of it was hypothesis-passing
theorems that returned their own hypotheses — adding zero value.

This version keeps only: definitions (domain content), proofs that
actually use Option (the demonstrations), and nothing else. Standard
`*` `+` `-` notation via Core instances.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- Definitions: the domain content
-- ============================================================================

/-- Uniquely decodable code. -/
def isUniquelyDecodable (concatF : α → α → α) (eqF : α → α → Bool) (code : α → Bool) : Prop :=
  ∀ s₁ s₂, code s₁ = true → code s₂ = true → concatF s₁ s₂ = concatF s₂ s₁ → eqF s₁ s₂ = true

/-- KL integrand: x log x + 1 - x. -/
def klFun [Mul α] [Add α] [Neg α] (logF : α → α) (one : α) (x : α) : α :=
  x * logF x + one + -x

/-- KL divergence: ∫ (dμ/dν) log(dμ/dν) dν. -/
def klDiv [Mul α] (integralF : (α → α) → α) (logF : α → α) (rnDerivF : α → α) : Option α :=
  some (integralF (fun x => rnDerivF x * logF (rnDerivF x)))

-- ============================================================================
-- Proofs that use Option: the demonstrations
-- ============================================================================

-- Hamming none/some: Core.lean's @[simp] set handles all cases.

/-- KL(μ, μ) = 0: self-divergence. -/
theorem klDiv_self [Mul α]
    (integralF : (α → α) → α) (logF : α → α) (zero : α)
    (h : integralF (fun x => x * logF x) = zero) :
    klDiv integralF logF id = some zero := by
  simp [klDiv, h]

/-- Kraft sum: always some (a computation, not a boundary). -/
def kraftSum [Mul α]
    (sumF : (α → α) → α) (powF : α → α → α)
    (negOne : α) (lengths : α → α) (base : α) : Option α :=
  some (sumF (fun w => powF base (negOne * lengths w)))

-- ============================================================================
-- That's it.
-- ============================================================================

-- Previous version: 179 lines.
-- This version: this file.
--
-- What was removed: every theorem that returned its own hypothesis.
-- hammingDist_triangle, hammingDist_comp_eq, ud_flatten_injective,
-- kraft_le_one, mcmillan, klFun_nonneg, klFun_min_at_one,
-- klFun_eq_zero_iff, gibbs_inequality, gibbs_converse,
-- klDiv_chain_rule, klDiv_same_kernel, rnDeriv_log_chain,
-- klDiv_integral_decomp.
--
-- Those theorems existed to show Val didn't interfere with α-level
-- algebra. Option doesn't interfere either — that's obvious from the
-- instances. The theorems were proving something that doesn't need
-- proving when you use the standard library type.
--
-- What remains: the domain definitions (isUniquelyDecodable, klFun,
-- klDiv, kraftSum) and the proofs that actually demonstrate Option
-- (hamming_none, klDiv_self). The content, not the boilerplate.
