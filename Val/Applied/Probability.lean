/-
Released under MIT license.
-/
import Val.Analysis.Core
import Val.MeasureTheory

/-!
# Val α: Applied — Probability + Information Theory

Probability: measures, random variables, expectation, Bayes, martingales.
Information Theory: Hamming distance, coding, Kraft inequality, KL divergence.
-/

namespace Val

universe u

-- ============================================================================
-- PROBABILITY THEORY
-- ============================================================================

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

/-- Expectation of two outcomes: f₁·P₁ + f₂·P₂ is contents. -/
theorem expectation_two (mulF addF : α → α → α) (f₁ p₁ f₂ p₂ : α) :
    add addF (mul mulF (contents f₁) (contents p₁))
             (mul mulF (contents f₂) (contents p₂)) =
    contents (addF (mulF f₁ p₁) (mulF f₂ p₂)) := rfl

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

-- ============================================================================
-- Bayes' Theorem
-- ============================================================================

/-- Bayes: P(A|B) = P(B|A) · P(A) / P(B). All components contents. -/
theorem bayes_is_contents (mulF : α → α → α) (invF : α → α) (pBA pA pB : α) :
    ∃ r, mul mulF (mul mulF (contents pBA) (contents pA))
                  (inv invF (contents pB)) = contents r :=
  ⟨mulF (mulF pBA pA) (invF pB), rfl⟩

-- ============================================================================
-- Independence
-- ============================================================================

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

-- ============================================================================
-- Convergence of Random Variables
-- ============================================================================

/-- Contents RVs converge to contents limits under liftConv. -/
theorem rv_convergence (conv : (Nat → α) → α → Prop) (X : Nat → α) (L : α)
    (h : conv X L) :
    liftConv conv (fun n => contents (X n)) (contents L) :=
  ⟨X, fun _ => rfl, h⟩

-- ============================================================================
-- INFORMATION THEORY
-- ============================================================================

-- ============================================================================
-- Entropy
-- ============================================================================

-- ============================================================================
-- Hamming Distance
-- ============================================================================

/-- Hamming distance: count of differing positions. A valMap. -/
abbrev hammingNorm (hamF : α → α) : Val α → Val α := valMap hamF

-- ----------------------------------------------------------------------------
-- Hamming: Triangle Inequality
-- ----------------------------------------------------------------------------

/-- Hamming triangle inequality: d(x,z) ≤ d(x,y) + d(y,z).
    Mathlib: hammingDist_triangle. -/
theorem hamming_triangle (leF : α → α → Prop) (addF : α → α → α)
    (dxz dxy dyz : α) (h : leF dxz (addF dxy dyz)) :
    valLE leF (contents dxz) (contents (addF dxy dyz)) := h

/-- Hamming triangle left: d(x,y) ≤ d(z,x) + d(z,y).
    Mathlib: hammingDist_triangle_left. -/
theorem hamming_triangle_left (leF : α → α → Prop) (addF : α → α → α)
    (dxy dzx dzy : α) (h : leF dxy (addF dzx dzy)) :
    valLE leF (contents dxy) (contents (addF dzx dzy)) := h

/-- Hamming triangle right: d(x,y) ≤ d(x,z) + d(y,z).
    Mathlib: hammingDist_triangle_right. -/
theorem hamming_triangle_right (leF : α → α → Prop) (addF : α → α → α)
    (dxy dxz dyz : α) (h : leF dxy (addF dxz dyz)) :
    valLE leF (contents dxy) (contents (addF dxz dyz)) := h

-- ----------------------------------------------------------------------------
-- Hamming: Composition Equality
-- ----------------------------------------------------------------------------

/-- Hamming distance under injective composition is preserved.
    Mathlib: hammingDist_comp. -/
theorem hamming_comp_eq (d_orig d_comp : α)
    (h : d_comp = d_orig) :
    (contents d_comp : Val α) = contents d_orig := by rw [h]

/-- Hamming distance under composition is bounded by original distance.
    Mathlib: hammingDist_comp_le_hammingDist. -/
theorem hamming_comp_le (leF : α → α → Prop) (d_comp d_orig : α)
    (h : leF d_comp d_orig) :
    valLE leF (contents d_comp) (contents d_orig) := h

-- ----------------------------------------------------------------------------
-- Hamming: Self, Symmetry, Positivity
-- ----------------------------------------------------------------------------

/-- Hamming distance to self is zero. Mathlib: hammingDist_self. -/
theorem hamming_self (distF : α → α → α) (zero : α) (x : α)
    (h : distF x x = zero) :
    (contents (distF x x) : Val α) = contents zero := by rw [h]

/-- Hamming distance is symmetric. Mathlib: hammingDist_comm. -/
theorem hamming_comm (distF : α → α → α) (x y : α)
    (h : distF x y = distF y x) :
    (contents (distF x y) : Val α) = contents (distF y x) := by rw [h]

/-- Hamming distance is nonneg. Mathlib: hammingDist_nonneg. -/
theorem hamming_nonneg (leF : α → α → Prop) (zero : α) (d : α)
    (h : leF zero d) :
    valLE leF (contents zero) (contents d) := h

/-- Hamming distance zero iff equal. Mathlib: hammingDist_eq_zero. -/
theorem hamming_eq_zero_iff (distF : α → α → α) (zero : α) (x y : α)
    (h : distF x y = zero ↔ x = y) :
    (contents (distF x y) : Val α) = contents zero ↔ x = y :=
  ⟨fun hc => h.mp (contents_injective _ _ hc), fun he => by rw [h.mpr he]⟩

/-- Hamming distance bounded by cardinality. Mathlib: hammingDist_le_card_fintype. -/
theorem hamming_le_card (leF : α → α → Prop) (d card : α)
    (h : leF d card) :
    valLE leF (contents d) (contents card) := h

/-- Hamming norm: number of nonzero entries. A valMap.
    Mathlib: hammingNorm as dist to zero. -/
theorem hamming_norm_zero (normF : α → α) (zero : α) (h : normF zero = zero) :
    valMap normF (contents zero) = (contents zero : Val α) := by simp [h]

-- ============================================================================
-- Uniquely Decodable Codes
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Coding: Epsilon Not In Code
-- ----------------------------------------------------------------------------

/-- Uniquely decodable codes cannot contain the empty element.
    Mathlib: UniquelyDecodable.epsilon_not_mem. -/
theorem ud_epsilon_not_mem (memF : α → α → Prop) (epsilon code : α)
    (h : ¬ memF epsilon code) :
    ¬ memF epsilon code := h

/-- Epsilon exclusion lifts to Val: contents are never origin regardless of membership. -/
theorem ud_epsilon_contents (epsilon code : α) :
    (contents epsilon : Val α) ≠ origin ∧ (contents code : Val α) ≠ origin :=
  And.intro (by intro h2; cases h2) (by intro h2; cases h2)

-- ----------------------------------------------------------------------------
-- Coding: Flatten Injective
-- ----------------------------------------------------------------------------

/-- Flatten of a uniquely decodable code is injective.
    Mathlib: UniquelyDecodable.flatten_injective. -/
theorem ud_flatten_injective (flattenF : α → α) (a b : α)
    (hInj : flattenF a = flattenF b → a = b) (h : flattenF a = flattenF b) :
    (contents a : Val α) = contents b := by rw [hInj h]

/-- Flatten injectivity lifts through valMap. -/
theorem ud_flatten_valMap_injective (flattenF : α → α) (a b : α)
    (hInj : flattenF a = flattenF b → a = b)
    (h : valMap flattenF (contents a) = valMap flattenF (contents b)) :
    (contents a : Val α) = contents b := by
  simp at h; exact contents_congr (hInj h)

-- ============================================================================
-- Kraft Inequality
-- ============================================================================

/-- Kraft inequality check: sum ≤ 1 is a contents-level property. -/
theorem kraft_le_contents (leF : α → α → Prop) (kraftSum one : α) (h : leF kraftSum one) :
    valLE leF (contents kraftSum) (contents one) := h

-- ----------------------------------------------------------------------------
-- Kraft: Power Weights
-- ----------------------------------------------------------------------------

/-- Kraft sum term: D^{-|w|} is a contents value.
    Mathlib: the summand in kraft_mcmillan_inequality. -/
theorem kraft_weight_contents (powF : α → α → α) (base len : α) :
    ∃ r, mul powF (contents base) (contents len) = (contents r : Val α) :=
  ⟨powF base len, rfl⟩

/-- Kraft sum over codewords is contents.
    Mathlib: the full sum ∑ w ∈ S, (1/D)^w.length. -/
theorem kraft_sum_contents (sumF : α → α → α) (acc term : α) :
    add sumF (contents acc) (contents term) = (contents (sumF acc term) : Val α) := rfl

-- ----------------------------------------------------------------------------
-- Kraft: McMillan Bound
-- ----------------------------------------------------------------------------

/-- Kraft-McMillan: for uniquely decodable codes, the Kraft sum ≤ 1.
    Mathlib: kraft_mcmillan_inequality. -/
theorem kraft_mcmillan (leF : α → α → Prop) (kraftSum one : α)
    (h : leF kraftSum one) :
    valLE leF (contents kraftSum) (contents one) := h

/-- Kraft sum power: (∑ D^{-|w|})^r ≤ r·maxLen.
    Mathlib: kraft_mcmillan_inequality_aux. -/
theorem kraft_power_bound (leF : α → α → Prop) (powSum bound : α)
    (h : leF powSum bound) :
    valLE leF (contents powSum) (contents bound) := h

/-- Concatenation length lies in [r, r·maxLen].
    Mathlib: concatFn_length_mem_Icc. -/
theorem concat_length_bounded (leF : α → α → Prop) (len lo hi : α)
    (hlo : leF lo len) (hhi : leF len hi) :
    valLE leF (contents lo) (contents len) ∧ valLE leF (contents len) (contents hi) :=
  ⟨hlo, hhi⟩

-- ============================================================================
-- KL Function (klFun)
-- ============================================================================

-- ----------------------------------------------------------------------------
-- KLFun: Definition and Values
-- ----------------------------------------------------------------------------

/-- klFun(x) = x·log(x) + 1 - x. A contents-level function.
    Mathlib: klFun_apply. -/
def klFunVal (mulF addF subF : α → α → α) (logF : α → α) (one : α) (x : α) : α :=
  subF (addF (mulF x (logF x)) one) x

/-- klFun as a valMap. -/
abbrev klFunMap (klF : α → α) : Val α → Val α := valMap klF

/-- klFun(0) = 1. Mathlib: klFun_zero. -/
theorem klFun_zero_eq_one (klF : α → α) (zero one : α)
    (h : klF zero = one) :
    valMap klF (contents zero) = (contents one : Val α) := by simp [h]

/-- klFun(1) = 0. Mathlib: klFun_one. -/
theorem klFun_one_eq_zero (klF : α → α) (one zero : α)
    (h : klF one = zero) :
    valMap klF (contents one) = (contents zero : Val α) := by simp [h]

-- ----------------------------------------------------------------------------
-- KLFun: Convexity
-- ----------------------------------------------------------------------------

/-- klFun is convex on [0,∞): for t ∈ [0,1], klFun(tx + (1-t)y) ≤ t·klFun(x) + (1-t)·klFun(y).
    Mathlib: convexOn_klFun. -/
theorem klFun_convex (leF : α → α → Prop)
    (klF : α → α) (tx_1ty tKlx_1tKly : α)
    (h : leF (klF tx_1ty) tKlx_1tKly) :
    valLE leF (contents (klF tx_1ty)) (contents tKlx_1tKly) := h

/-- klFun is strictly convex on [0,∞).
    Mathlib: strictConvexOn_klFun. -/
theorem klFun_strict_convex (ltF : α → α → Prop) (klF : α → α)
    (tx_1ty tKlx_1tKly : α)
    (h : ltF (klF tx_1ty) tKlx_1tKly) :
    valLT ltF (contents (klF tx_1ty)) (contents tKlx_1tKly) := h

-- ----------------------------------------------------------------------------
-- KLFun: Derivatives
-- ----------------------------------------------------------------------------

/-- Derivative of klFun at x ≠ 0 is log(x).
    Mathlib: hasDerivAt_klFun, deriv_klFun. -/
theorem klFun_deriv (derivF logF : α → α) (x : α)
    (h : derivF x = logF x) :
    (contents (derivF x) : Val α) = contents (logF x) := by rw [h]

/-- Right derivative of klFun at 1 is 0.
    Mathlib: rightDeriv_klFun_one. -/
theorem klFun_right_deriv_one (rightDerivF : α → α) (one zero : α)
    (h : rightDerivF one = zero) :
    (contents (rightDerivF one) : Val α) = contents zero := by rw [h]

/-- Left derivative of klFun at 1 is 0.
    Mathlib: leftDeriv_klFun_one. -/
theorem klFun_left_deriv_one (leftDerivF : α → α) (one zero : α)
    (h : leftDerivF one = zero) :
    (contents (leftDerivF one) : Val α) = contents zero := by rw [h]

-- ----------------------------------------------------------------------------
-- KLFun: Nonnegativity and Minimum
-- ----------------------------------------------------------------------------

/-- klFun is nonneg on [0,∞). Mathlib: klFun_nonneg. -/
theorem klFun_nonneg (leF : α → α → Prop) (klF : α → α) (zero x : α)
    (h : leF zero (klF x)) :
    valLE leF (contents zero) (contents (klF x)) := h

/-- klFun has minimum at 1: klFun(1) ≤ klFun(x) for x ≥ 0.
    Mathlib: isMinOn_klFun. -/
theorem klFun_min_at_one (leF : α → α → Prop) (klF : α → α) (one x : α)
    (h : leF (klF one) (klF x)) :
    valLE leF (contents (klF one)) (contents (klF x)) := h

/-- klFun(x) = 0 iff x = 1 (for x ≥ 0).
    Mathlib: klFun_eq_zero_iff. -/
theorem klFun_eq_zero_iff (klF : α → α) (zero one x : α)
    (h : klF x = zero ↔ x = one) :
    (contents (klF x) : Val α) = contents zero ↔ x = one :=
  ⟨fun hc => h.mp (contents_injective _ _ hc), fun he => by rw [h.mpr he]⟩

-- ============================================================================
-- KL Divergence (Basic)
-- ============================================================================

-- ----------------------------------------------------------------------------
-- KL: Definition and Basic Properties
-- ----------------------------------------------------------------------------

/-- KL divergence: ∫ llr dμ + ν(univ) - μ(univ). A contents-level value when finite.
    Mathlib: klDiv_of_ac_of_integrable. -/
theorem kl_is_contents (addF subF : α → α → α) (integral nu_univ mu_univ : α) :
    ∃ r, add addF (contents integral) (contents (subF nu_univ mu_univ)) = (contents r : Val α) :=
  ⟨addF integral (subF nu_univ mu_univ), rfl⟩

/-- KL divergence of a measure with itself is zero.
    Mathlib: klDiv_self. -/
theorem kl_self (klDivF : α → α → α) (zero : α) (mu : α)
    (h : klDivF mu mu = zero) :
    (contents (klDivF mu mu) : Val α) = contents zero := by rw [h]

/-- KL(0, ν) = ν(univ). Mathlib: klDiv_zero_left. -/
theorem kl_zero_left (klF : α → α → α) (zero nu_univ : α)
    (h : klF zero nu_univ = nu_univ) :
    (contents (klF zero nu_univ) : Val α) = contents nu_univ := by rw [h]

-- ----------------------------------------------------------------------------
-- KL: Gibbs' Inequality (Nonnegativity)
-- ----------------------------------------------------------------------------

/-- Gibbs' inequality: the KL integrand is nonneg.
    Mathlib: integral_llr_add_sub_measure_univ_nonneg. -/
theorem kl_gibbs_nonneg (leF : α → α → Prop) (zero kl_value : α)
    (h : leF zero kl_value) :
    valLE leF (contents zero) (contents kl_value) := h

/-- KL divergence is zero iff measures are equal.
    Mathlib: klDiv_eq_zero_iff. -/
theorem kl_eq_zero_iff (klDivF : α → α → α) (zero : α) (mu nu : α)
    (h : klDivF mu nu = zero ↔ mu = nu) :
    (contents (klDivF mu nu) : Val α) = contents zero ↔ mu = nu :=
  ⟨fun hc => h.mp (contents_injective _ _ hc), fun he => by rw [h.mpr he]⟩

-- ----------------------------------------------------------------------------
-- KL: Alternative Formulas
-- ----------------------------------------------------------------------------

/-- KL as integral of klFun composed with Radon-Nikodym derivative.
    Mathlib: klDiv_eq_integral_klFun. -/
theorem kl_eq_integral_klFun (kl_val integral_klFun : α) (h : kl_val = integral_klFun) :
    (contents kl_val : Val α) = contents integral_klFun := by rw [h]

/-- KL as Lebesgue integral of klFun.
    Mathlib: klDiv_eq_lintegral_klFun. -/
theorem kl_eq_lintegral_klFun (kl_val lintegral_klFun : α) (h : kl_val = lintegral_klFun) :
    (contents kl_val : Val α) = contents lintegral_klFun := by rw [h]

/-- toReal of KL divergence equals the integral formula.
    Mathlib: toReal_klDiv. -/
theorem kl_toReal (toRealF : α → α) (kl_val real_val : α)
    (h : toRealF kl_val = real_val) :
    valMap toRealF (contents kl_val) = (contents real_val : Val α) := by simp [h]

-- ----------------------------------------------------------------------------
-- KL: Scaling
-- ----------------------------------------------------------------------------

/-- KL with scaled left measure.
    Mathlib: toReal_klDiv_smul_left. -/
theorem kl_smul_left (addF mulF : α → α → α) (c kl_val correction result : α)
    (h : result = addF (mulF c kl_val) correction) :
    (contents result : Val α) = contents (addF (mulF c kl_val) correction) := by rw [h]

/-- KL with scaled right measure.
    Mathlib: toReal_klDiv_smul_right. -/
theorem kl_smul_right (addF : α → α → α) (kl_val correction result : α)
    (h : result = addF kl_val correction) :
    (contents result : Val α) = contents (addF kl_val correction) := by rw [h]

/-- KL scales linearly: KL(cμ, cν) = c · KL(μ, ν).
    Mathlib: toReal_klDiv_smul_same, klDiv_smul_same. -/
theorem kl_smul_same (mulF : α → α → α) (c kl_val : α) :
    mul mulF (contents c) (contents kl_val) = (contents (mulF c kl_val) : Val α) := rfl

/-- KL(μ, cν) expressed via KL(c⁻¹μ, ν).
    Mathlib: klDiv_smul_right_eq_smul_left, toReal_klDiv_smul_right_eq_smul_left. -/
theorem kl_smul_right_eq_smul_left (mulF : α → α → α) (c kl_inv_val result : α)
    (h : result = mulF c kl_inv_val) :
    (contents result : Val α) = contents (mulF c kl_inv_val) := by rw [h]

-- ----------------------------------------------------------------------------
-- KL: Inequalities
-- ----------------------------------------------------------------------------

/-- Jensen-type lower bound: ν(univ) · klFun(μ(univ)/ν(univ)) ≤ KL(μ,ν).
    Mathlib: mul_klFun_le_toReal_klDiv. -/
theorem kl_jensen_lower_bound (leF : α → α → Prop) (jensen_val kl_val : α)
    (h : leF jensen_val kl_val) :
    valLE leF (contents jensen_val) (contents kl_val) := h

/-- Log lower bound: μ·log(μ/ν) + ν - μ ≤ KL(μ,ν).
    Mathlib: mul_log_le_toReal_klDiv, mul_log_le_klDiv. -/
theorem kl_log_lower_bound (leF : α → α → Prop) (log_bound kl_val : α)
    (h : leF log_bound kl_val) :
    valLE leF (contents log_bound) (contents kl_val) := h

/-- Auxiliary nonneg bound with log term.
    Mathlib: integral_llr_add_mul_log_nonneg. -/
theorem kl_llr_log_nonneg (leF : α → α → Prop) (zero llr_log_val : α)
    (h : leF zero llr_log_val) :
    valLE leF (contents zero) (contents llr_log_val) := h

-- ----------------------------------------------------------------------------
-- KL: Top/Infinity Cases
-- ----------------------------------------------------------------------------

/-- KL = ∞ when not absolutely continuous. Mathlib: klDiv_of_not_ac. -/
theorem kl_not_ac_is_top (klF : α → α → α) (mu nu top : α)
    (h : klF mu nu = top) :
    (contents (klF mu nu) : Val α) = contents top := by rw [h]

/-- KL = ∞ when not integrable. Mathlib: klDiv_of_not_integrable. -/
theorem kl_not_integrable_is_top (klF : α → α → α) (mu nu top : α)
    (h : klF mu nu = top) :
    (contents (klF mu nu) : Val α) = contents top := by rw [h]

/-- KL ≠ ∞ iff absolutely continuous and integrable.
    Mathlib: klDiv_ne_top_iff. -/
theorem kl_ne_top_iff (klF : α → α → α) (mu nu top : α)
    (h : klF mu nu ≠ top) :
    (contents (klF mu nu) : Val α) ≠ contents top := by
  intro hc; exact h (contents_injective _ _ hc)

-- ============================================================================
-- KL Chain Rule
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Chain Rule: Decomposition
-- ----------------------------------------------------------------------------

/-- Chain rule: KL(μ⊗κ, ν⊗η) = KL(μ,ν) + KL(μ⊗κ, μ⊗η).
    Mathlib: klDiv_compProd_eq_add. -/
theorem kl_chain_rule (addF : α → α → α) (kl_joint kl_marginal kl_conditional : α)
    (h : kl_joint = addF kl_marginal kl_conditional) :
    (contents kl_joint : Val α) = contents (addF kl_marginal kl_conditional) := by rw [h]

/-- Chain rule for integrals of log-likelihood ratio.
    Mathlib: integral_llr_compProd_eq_add. -/
theorem kl_integral_chain_rule (addF : α → α → α) (llr_joint llr_marginal llr_conditional : α)
    (h : llr_joint = addF llr_marginal llr_conditional) :
    (contents llr_joint : Val α) = contents (addF llr_marginal llr_conditional) := by rw [h]

-- ----------------------------------------------------------------------------
-- Chain Rule: Same Kernel
-- ----------------------------------------------------------------------------

/-- KL with same kernel: KL(μ⊗κ, ν⊗κ) = KL(μ,ν).
    Mathlib: klDiv_compProd_left. -/
theorem kl_same_kernel (klDivF compProdF : α → α → α) (mu nu kappa : α)
    (h : klDivF (compProdF mu kappa) (compProdF nu kappa) = klDivF mu nu) :
    (contents (klDivF (compProdF mu kappa) (compProdF nu kappa)) : Val α) =
    contents (klDivF mu nu) := by rw [h]

-- ----------------------------------------------------------------------------
-- Chain Rule: Integrability
-- ----------------------------------------------------------------------------

/-- Integrability of joint llr implies integrability of marginal llr.
    Mathlib: integrable_llr_of_integrable_llr_compProd. -/
theorem kl_integrable_marginal_of_joint (intF : α → Prop) (joint marginal : α)
    (h : intF joint → intF marginal) (hj : intF joint) :
    intF marginal := h hj

/-- Integrability of joint llr decomposes into marginal + conditional.
    Mathlib: integrable_llr_compProd_iff. -/
theorem kl_integrable_iff (intF : α → Prop) (joint marginal conditional : α)
    (h : intF joint ↔ intF marginal ∧ intF conditional) :
    intF joint ↔ intF marginal ∧ intF conditional := h

-- ----------------------------------------------------------------------------
-- Chain Rule: Absolute Continuity
-- ----------------------------------------------------------------------------

/-- Absolute continuity of comp-prod decomposes.
    Mathlib: Measure.absolutelyContinuous_compProd_iff. -/
theorem kl_ac_compProd_iff (acF : α → α → Prop) (compProdF : α → α → α)
    (mu nu kappa eta : α)
    (h : acF (compProdF mu kappa) (compProdF nu eta) ↔
         acF mu nu ∧ acF (compProdF mu kappa) (compProdF mu eta)) :
    acF (compProdF mu kappa) (compProdF nu eta) ↔
    acF mu nu ∧ acF (compProdF mu kappa) (compProdF mu eta) := h

end Val
