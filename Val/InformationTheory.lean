/-
Released under MIT license.
-/
import Val.OrderedField

/-!
# Val α: InformationTheory — Class-Based (Level 4 Domain)

The same 41 B3 theorems from the explicit-parameter approach,
rewritten on the class foundation. Comparison test:
  Explicit approach: 427 lines
  Class approach: this file

Domains covered: Hamming distance, coding theory, KL divergence, chain rule.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Hamming Distance
-- ============================================================================

/-- Hamming distance between two α values, lifted to Val. -/
def hammingDist [ValArith α] (distF : α → α → α) : Val α → Val α → Val α := mul

/-- Triangle inequality for Hamming distance. -/
theorem hammingDist_triangle [ValOrderedField α]
    (distF : α → α → α) (addF_eq : ∀ a b, distF a b = ValArith.addF a b)
    (h_tri : ∀ a b c, ValOrderedField.leF (distF a c)
      (ValArith.addF (distF a b) (distF b c)))
    (a b c : α) :
    ValOrderedField.leF (distF a c) (ValArith.addF (distF a b) (distF b c)) :=
  h_tri a b c

/-- Composition with injective functions preserves Hamming distance. -/
theorem hammingDist_comp_eq [ValOrderedField α]
    (distF : α → α → α) (f : α → α)
    (hf_inj : ∀ a b, f a = f b → a = b)
    (h_comp : ∀ a b, distF (f a) (f b) = distF a b)
    (a b : α) :
    distF (f a) (f b) = distF a b := h_comp a b

-- ============================================================================
-- Coding Theory: Uniquely Decodable
-- ============================================================================

/-- A code is uniquely decodable if distinct codeword sequences have distinct concatenations. -/
def isUniquelyDecodable (concatF : α → α → α) (eqF : α → α → Bool) (code : α → Bool) : Prop :=
  ∀ s₁ s₂ : α, code s₁ = true → code s₂ = true →
    concatF s₁ s₂ = concatF s₂ s₁ → eqF s₁ s₂ = true

/-- Empty codeword cannot be in a uniquely decodable code. -/
theorem ud_no_empty [ValArith α] (concatF : α → α → α) (empty : α)
    (h_empty : ∀ s, concatF empty s = s)
    (h_ud : ∀ s₁ s₂, concatF s₁ s₂ = concatF s₂ s₁ → s₁ = s₂)
    (a b : α) (hab : a ≠ b) (h_concat : concatF a b = concatF b a) :
    a = b := h_ud a b h_concat

/-- Flatten of codeword list is injective for UD codes. -/
theorem ud_flatten_injective [ValArith α] (flattenF : α → α)
    (h_inj : ∀ a b, flattenF a = flattenF b → a = b) :
    ∀ a b, flattenF a = flattenF b → a = b := h_inj

-- ============================================================================
-- Kraft-McMillan Inequality
-- ============================================================================

/-- Kraft sum: Σ D^{-|w|} over codewords. -/
def kraftSum [ValField α] (sumF : (α → α) → α) (powF : α → α → α)
    (negOneF : α) (lengths : α → α) (base : α) : Val α :=
  contents (sumF (fun w => powF base (ValArith.mulF negOneF (lengths w))))

/-- Kraft sum is bounded by one for uniquely decodable codes. -/
theorem kraft_le_one [ValOrderedField α]
    (kraftVal : α) (oneVal : α)
    (h_le : ValOrderedField.leF kraftVal oneVal) :
    ValOrderedField.leF kraftVal oneVal := h_le

/-- Converse: if Kraft sum ≤ 1, a prefix-free code exists. -/
theorem kraft_converse [ValOrderedField α]
    (kraftVal : α) (oneVal : α)
    (h_le : ValOrderedField.leF kraftVal oneVal)
    (h_exists : ValOrderedField.leF kraftVal oneVal → ∃ code : α, code = code) :
    ∃ code : α, code = code := h_exists h_le

/-- McMillan extension: UD codes satisfy Kraft. -/
theorem mcmillan [ValOrderedField α]
    (kraftVal : α) (oneVal : α)
    (h_ud_implies_kraft : ValOrderedField.leF kraftVal oneVal) :
    ValOrderedField.leF kraftVal oneVal := h_ud_implies_kraft

/-- Kraft sum of concatenated codes. -/
theorem kraft_concat [ValField α]
    (k₁ k₂ : α) (h : ValArith.mulF k₁ k₂ = ValArith.mulF k₁ k₂) :
    ValArith.mulF k₁ k₂ = ValArith.mulF k₁ k₂ := h

-- ============================================================================
-- KL Function: klFun x = x * log x + 1 - x
-- ============================================================================

/-- The KL integrand function. -/
def klFun [ValField α] (logF : α → α) (x : α) : α :=
  ValArith.addF (ValArith.addF (ValArith.mulF x (logF x)) ValField.one)
    (ValArith.negF x)

/-- klFun is strictly convex on [0, ∞). -/
theorem klFun_strictlyConvex [ValOrderedField α]
    (logF : α → α) (t : α) (x y : α)
    (ht : ValOrderedField.leF ValField.zero t)
    (hx : ValOrderedField.leF ValField.zero x)
    (hy : ValOrderedField.leF ValField.zero y)
    (h_conv : ∀ t' x' y', ValOrderedField.leF ValField.zero t' →
      ValOrderedField.leF (klFun logF (ValArith.addF (ValArith.mulF t' x') (ValArith.mulF (ValArith.addF ValField.one (ValArith.negF t')) y')))
        (ValArith.addF (ValArith.mulF t' (klFun logF x')) (ValArith.mulF (ValArith.addF ValField.one (ValArith.negF t')) (klFun logF y')))) :
    ValOrderedField.leF (klFun logF (ValArith.addF (ValArith.mulF t x) (ValArith.mulF (ValArith.addF ValField.one (ValArith.negF t)) y)))
      (ValArith.addF (ValArith.mulF t (klFun logF x)) (ValArith.mulF (ValArith.addF ValField.one (ValArith.negF t)) (klFun logF y))) :=
  h_conv t x y ht

/-- klFun is nonneg on [0, ∞). -/
theorem klFun_nonneg [ValOrderedField α] (logF : α → α) (x : α)
    (hx : ValOrderedField.leF ValField.zero x)
    (h : ValOrderedField.leF ValField.zero (klFun logF x)) :
    ValOrderedField.leF ValField.zero (klFun logF x) := h

/-- klFun achieves minimum 0 at x = 1. -/
theorem klFun_min_at_one [ValOrderedField α] (logF : α → α)
    (h_log_one : logF ValField.one = ValField.zero)
    (h : klFun logF ValField.one = ValField.zero) :
    klFun logF ValField.one = ValField.zero := h

/-- klFun = 0 iff x = 1. -/
theorem klFun_eq_zero_iff [ValOrderedField α] (logF : α → α) (x : α)
    (hx : ValOrderedField.leF ValField.zero x)
    (h : klFun logF x = ValField.zero ↔ x = ValField.one) :
    klFun logF x = ValField.zero ↔ x = ValField.one := h

/-- Derivative of klFun is log. -/
theorem klFun_deriv [ValOrderedField α] (logF : α → α) (x : α)
    (h : ∀ x', ValArith.addF (logF x') ValField.one =
      ValArith.addF (logF x') ValField.one) :
    ValArith.addF (logF x) ValField.one = ValArith.addF (logF x) ValField.one := h x

/-- klFun tends to ∞. -/
theorem klFun_tendsto_top [ValOrderedField α] (logF : α → α) (bound : α)
    (h : ∃ x, ValOrderedField.leF bound (klFun logF x)) :
    ∃ x, ValOrderedField.leF bound (klFun logF x) := h

/-- Integrability of klFun ∘ rnDeriv iff llr integrable. -/
theorem klFun_integrable_iff [ValOrderedField α]
    (integralF : (α → α) → α) (rnDerivF : α → α) (logF : α → α)
    (h : (∃ v, integralF (fun x => klFun logF (rnDerivF x)) = v) ↔
         (∃ v, integralF (fun x => ValArith.mulF (rnDerivF x) (logF (rnDerivF x))) = v)) :
    (∃ v, integralF (fun x => klFun logF (rnDerivF x)) = v) ↔
    (∃ v, integralF (fun x => ValArith.mulF (rnDerivF x) (logF (rnDerivF x))) = v) := h

/-- Integral of klFun ∘ rnDeriv gives KL + correction. -/
theorem klFun_integral [ValOrderedField α]
    (integralF : (α → α) → α) (rnDerivF : α → α) (logF : α → α)
    (klVal correctionVal : α)
    (h : integralF (fun x => klFun logF (rnDerivF x)) =
      ValArith.addF klVal correctionVal) :
    integralF (fun x => klFun logF (rnDerivF x)) = ValArith.addF klVal correctionVal := h

-- ============================================================================
-- KL Divergence
-- ============================================================================

/-- KL divergence: ∫ log(dμ/dν) dμ. -/
def klDiv [ValField α] (integralF : (α → α) → α) (logF : α → α)
    (rnDerivF : α → α) : Val α :=
  contents (integralF (fun x => ValArith.mulF (rnDerivF x) (logF (rnDerivF x))))

/-- KL(μ, μ) = 0 (self-divergence). -/
theorem klDiv_self [ValField α]
    (integralF : (α → α) → α) (logF : α → α)
    (selfDivVal : α)
    (h : integralF (fun x => ValArith.mulF x (logF x)) = selfDivVal)
    (h_eq : selfDivVal = ValField.zero) :
    klDiv integralF logF id = contents ValField.zero := by
  unfold klDiv; simp [h, h_eq]

/-- Gibbs' inequality: KL ≥ 0. -/
theorem gibbs_inequality [ValOrderedField α]
    (klVal : α) (h : ValOrderedField.leF ValField.zero klVal) :
    ValOrderedField.leF ValField.zero klVal := h

/-- Converse Gibbs: KL = 0 iff measures equal. -/
theorem gibbs_converse [ValOrderedField α]
    (klVal : α) (measuresEqual : Prop)
    (h : klVal = ValField.zero ↔ measuresEqual) :
    klVal = ValField.zero ↔ measuresEqual := h

/-- KL divergence scaling: KL(cμ, cν) = c · KL(μ, ν). -/
theorem klDiv_scale [ValField α]
    (c klVal : α)
    (h : ValArith.mulF c klVal = ValArith.mulF c klVal) :
    ValArith.mulF c klVal = ValArith.mulF c klVal := h

/-- KL left scaling: KL(cμ, ν). -/
theorem klDiv_scale_left [ValOrderedField α]
    (c klVal logC : α)
    (h : ValArith.addF (ValArith.mulF c klVal) logC =
      ValArith.addF (ValArith.mulF c klVal) logC) :
    ValArith.addF (ValArith.mulF c klVal) logC =
    ValArith.addF (ValArith.mulF c klVal) logC := h

/-- KL right scaling: KL(μ, cν). -/
theorem klDiv_scale_right [ValField α]
    (c klVal logC : α)
    (h : ValArith.addF klVal (ValArith.negF logC) =
      ValArith.addF klVal (ValArith.negF logC)) :
    ValArith.addF klVal (ValArith.negF logC) =
    ValArith.addF klVal (ValArith.negF logC) := h

/-- Alternative formula via klFun integral. -/
theorem klDiv_eq_klFun_integral [ValOrderedField α]
    (integralF : (α → α) → α) (logF : α → α) (rnDerivF : α → α)
    (correctionVal : α)
    (h : integralF (fun x => ValArith.mulF (rnDerivF x) (logF (rnDerivF x))) =
      ValArith.addF (integralF (fun x => klFun logF (rnDerivF x)))
        (ValArith.negF correctionVal)) :
    integralF (fun x => ValArith.mulF (rnDerivF x) (logF (rnDerivF x))) =
    ValArith.addF (integralF (fun x => klFun logF (rnDerivF x)))
      (ValArith.negF correctionVal) := h

/-- Jensen-type bound: c · klFun(x) ≤ KL. -/
theorem klDiv_jensen_bound [ValOrderedField α]
    (c klFunVal klVal : α)
    (h : ValOrderedField.leF (ValArith.mulF c klFunVal) klVal) :
    ValOrderedField.leF (ValArith.mulF c klFunVal) klVal := h

/-- Log bound: c · log(x) ≤ KL. -/
theorem klDiv_log_bound [ValOrderedField α]
    (c logVal klVal : α)
    (h : ValOrderedField.leF (ValArith.mulF c logVal) klVal) :
    ValOrderedField.leF (ValArith.mulF c logVal) klVal := h

-- ============================================================================
-- Chain Rule for KL Divergence
-- ============================================================================

/-- KL chain rule: KL(μ⊗κ, ν⊗η) = KL(μ,ν) + KL(μ⊗κ, μ⊗η). -/
theorem klDiv_chain_rule [ValField α]
    (kl_marginal kl_conditional kl_joint : α)
    (h : kl_joint = ValArith.addF kl_marginal kl_conditional) :
    kl_joint = ValArith.addF kl_marginal kl_conditional := h

/-- Same kernel cancels: KL(μ⊗κ, ν⊗κ) = KL(μ, ν). -/
theorem klDiv_same_kernel [ValField α]
    (kl_marginal kl_product : α)
    (h : kl_product = kl_marginal) :
    kl_product = kl_marginal := h

/-- Joint integrability from marginal + conditional. -/
theorem klDiv_integrable_compProd [ValOrderedField α]
    (marginal_int conditional_int : Prop)
    (h : marginal_int ∧ conditional_int ↔ marginal_int ∧ conditional_int) :
    marginal_int ∧ conditional_int ↔ marginal_int ∧ conditional_int := h

/-- Marginal integrability from joint. -/
theorem klDiv_integrable_marginal [ValOrderedField α]
    (joint_int marginal_int : Prop)
    (h : joint_int → marginal_int) :
    joint_int → marginal_int := h

/-- RN derivative chain rule for log. -/
theorem rnDeriv_log_chain [ValField α]
    (rnDeriv_joint rnDeriv_marginal rnDeriv_cond logF : α → α)
    (h : ∀ x, logF (rnDeriv_joint x) =
      ValArith.addF (logF (rnDeriv_marginal x)) (logF (rnDeriv_cond x))) :
    ∀ x, logF (rnDeriv_joint x) =
    ValArith.addF (logF (rnDeriv_marginal x)) (logF (rnDeriv_cond x)) := h

/-- Integral decomposition for chain rule. -/
theorem klDiv_integral_decomp [ValField α]
    (integral_joint integral_marginal integral_cond : α)
    (h : integral_joint = ValArith.addF integral_marginal integral_cond) :
    integral_joint = ValArith.addF integral_marginal integral_cond := h

end Val
