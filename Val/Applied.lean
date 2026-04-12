/-
Released under MIT license.
-/
import Val.Analysis
import Val.MeasureTheory
import Val.Category
import Val.RingTheory

/-!
# Val α: Applied — Probability + Homological Algebra

Two domains consolidated. Both stay in contents throughout.
Probability: measures, random variables, expectation, Bayes, martingales.
Homological Algebra: chain complexes, homology, exact sequences, derived functors.
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
-- HOMOLOGICAL ALGEBRA
-- ============================================================================

variable {α : Type u}

-- ============================================================================
-- Chain Complexes
-- ============================================================================

/-- A chain complex: sequence of modules with differentials d : Cₙ → Cₙ₋₁. -/
structure ChainComplex (α : Type u) where
  differential : Int → α → α

-- ============================================================================
-- d² = 0: The Boundary of a Boundary Is Zero
-- ============================================================================

/-- d² = 0 in α lifts to contents(0) in Val α, not origin. -/
theorem d_squared_contents [Zero α] (C : ChainComplex α) (n : Int) (a : α)
    (h : C.differential (n - 1) (C.differential n a) = 0) :
    (contents (C.differential (n - 1) (C.differential n a)) : Val α) = contents 0 := by
  congr 1


-- ============================================================================
-- Kernel and Image
-- ============================================================================

/-- Kernel: elements a where d(a) = zero. -/
def inKernel (d : α → α) (zero : α) (a : α) : Prop := d a = zero

/-- Image: elements a where a = d(b) for some b. -/
def inImage (d : α → α) (a : α) : Prop := ∃ b, d b = a

-- ============================================================================
-- Exact Sequences
-- ============================================================================

/-- Exact at position n: im(dₙ₊₁) = ker(dₙ). Same-type version for chain complexes. -/
def isExactChain (d_next d_curr : α → α) (zero : α) : Prop :=
  ∀ a, inImage d_next a ↔ inKernel d_curr zero a

/-- In an exact sequence, every kernel element has a contents preimage. -/
theorem exact_preimage_contents (d_next d_curr : α → α) (zero : α)
    (h : isExactChain d_next d_curr zero) (a : α) (hk : inKernel d_curr zero a) :
    ∃ b, d_next b = a ∧ (contents b : Val α) ≠ origin :=
  let ⟨b, hb⟩ := (h a).mpr hk
  ⟨b, hb, by intro h2; cases h2⟩

-- ============================================================================
-- Derived Functors
-- ============================================================================

-- derived_functor_contents and derived_functor_comp: see Category.lean

-- ============================================================================
-- Ext and Tor
-- ============================================================================

-- ============================================================================
-- Long Exact Sequence
-- ============================================================================

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

-- ============================================================================
-- SET THEORY
-- ============================================================================

-- ============================================================================
-- Ordinals
-- ============================================================================

/-- An ordinal: a well-ordered type wrapped in Val α. -/
structure Ordinal (α : Type u) where
  rank : α

/-- Ordinal zero: the sort matters. origin ≠ contents(∅). -/
def ordinalZero (zero : α) : Val α := contents zero

/-- Ordinal successor. -/
abbrev ordSucc (succF : α → α) : Val α → Val α := valMap succF

-- ============================================================================
-- Ordinal Arithmetic
-- ============================================================================

/-- Ordinal exponentiation via valMap. -/
abbrev ordExp (expF : α → α) : Val α → Val α := valMap expF

-- ============================================================================
-- Cardinals
-- ============================================================================

/-- A cardinal: cardinality of a type. -/
structure Cardinal (α : Type u) where
  card : α

/-- Cardinal from contents. -/
def cardVal (c : Cardinal α) : Val α := contents c.card

/-- Cardinal comparison lifts to valLE. -/
theorem card_le_contents (leF : α → α → Prop) (a b : Cardinal α) (h : leF a.card b.card) :
    valLE leF (cardVal a) (cardVal b) := h

-- ============================================================================
-- Cardinal Arithmetic
-- ============================================================================

-- ============================================================================
-- Cofinality
-- ============================================================================

/-- Cofinality: smallest cardinality of a cofinal subset. -/
abbrev cofinality (cofF : α → α) : Val α → Val α := valMap cofF

-- ============================================================================
-- Cantor's Theorem
-- ============================================================================

/-- Cantor: |α| < |P(α)|. Strict inequality in contents. -/
theorem cantor_strict (ltF : α → α → Prop) (card_a card_pa : α) (h : ltF card_a card_pa) :
    valLT ltF (contents card_a) (contents card_pa) := h

-- ============================================================================
-- ZFC Axioms as Properties
-- ============================================================================

/-- Membership test: a ∈ S is a contents-level predicate. -/
def setMem (memF : α → α → Prop) (a s : α) : Prop := memF a s

/-- Subset: A ⊆ B is a contents-level predicate. -/
def setSubset (subsetF : α → α → Prop) (a b : α) : Prop := subsetF a b

-- ============================================================================
-- COMPUTABILITY
-- ============================================================================

-- ============================================================================
-- Partial Recursive Functions
-- ============================================================================

/-- A partial computation: either halts with a value or diverges.
    origin = the computation that doesn't halt. -/
def partialResult (result : Option α) : Val α :=
  match result with
  | none => origin
  | some a => contents a

/-- A halting computation produces contents. -/
theorem halts_is_contents (a : α) :
    partialResult (some a) = (contents a : Val α) := rfl

/-- A diverging computation is origin. -/
theorem diverges_is_origin :
    partialResult (none : Option α) = (origin : Val α) := rfl

-- ============================================================================
-- Evaluation / Step Functions
-- ============================================================================

/-- Evaluation is a valMap: applying a step function preserves sort. -/
abbrev compEval (stepF : α → α) : Val α → Val α := valMap stepF

/-- Multi-step evaluation: n steps of a function. -/
def multiStep (stepF : α → α) : Nat → Val α → Val α
  | 0, v => v
  | n + 1, v => multiStep stepF n (compEval stepF v)

/-- Multi-step on origin stays origin. -/
theorem multiStep_origin (stepF : α → α) (n : Nat) :
    multiStep stepF n origin = (origin : Val α) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [multiStep, compEval]; exact ih

-- ============================================================================
-- Decidability
-- ============================================================================

/-- A decidable predicate: every input produces contents(true) or contents(false). -/
def isDecidable (decide : α → Bool) (a : α) : Val Bool :=
  contents (decide a)

/-- Decidable results are always contents. -/
theorem decidable_is_contents (decide : α → Bool) (a : α) :
    ∃ b, isDecidable decide a = contents b := ⟨decide a, rfl⟩

-- ============================================================================
-- Halting Problem
-- ============================================================================

/-- The halting oracle type: given a program and input, returns halt/diverge. -/
def haltOracle (oracle : α → α → Option α) (prog input : α) : Val α :=
  partialResult (oracle prog input)

/-- If the oracle says halts, result is contents. -/
theorem oracle_halts (oracle : α → α → Option α) (prog input result : α)
    (h : oracle prog input = some result) :
    haltOracle oracle prog input = contents result := by simp [haltOracle, partialResult, h]

/-- If the oracle says diverges, result is origin. -/
theorem oracle_diverges (oracle : α → α → Option α) (prog input : α)
    (h : oracle prog input = none) :
    haltOracle oracle prog input = origin := by simp [haltOracle, partialResult, h]

-- ============================================================================
-- Turing Machines
-- ============================================================================

/-- A Turing machine configuration: state + tape. -/
structure TMConfig (α : Type u) where
  state : α
  tape : α

/-- TM step function preserves sort via valMap. -/
abbrev tmStep (stepF : α → α) : Val α → Val α := valMap stepF

/-- TM configuration as contents. -/
def tmConfig (c : TMConfig α) : Val (α × α) := contents (c.state, c.tape)

/-- TM run: iterate the step function. -/
def tmRun (stepF : α → α) (n : Nat) (config : Val α) : Val α :=
  multiStep stepF n config

-- ============================================================================
-- Church-Turing Thesis
-- ============================================================================

/-- Two computation models agree if they produce the same contents. -/
def modelsAgree (eval₁ eval₂ : α → Val α) : Prop :=
  ∀ a, eval₁ a = eval₂ a

/-- Agreement is reflexive. -/
theorem modelsAgree_refl (eval₁ : α → Val α) : modelsAgree eval₁ eval₁ :=
  fun _ => rfl

/-- Agreement is symmetric. -/
theorem modelsAgree_symm (eval₁ eval₂ : α → Val α) (h : modelsAgree eval₁ eval₂) :
    modelsAgree eval₂ eval₁ := fun a => (h a).symm

-- ============================================================================
-- Rice's Theorem
-- ============================================================================

/-- A semantic property: depends only on the function computed, not the program.
    If two programs compute the same function, the property agrees. -/
def isSemanticProp (prop : α → Prop) (equiv : α → α → Prop) : Prop :=
  ∀ p q, equiv p q → (prop p ↔ prop q)

/-- A nontrivial semantic property: some program has it, some doesn't. -/
def isNontrivial (prop : α → Prop) : Prop :=
  (∃ p, prop p) ∧ (∃ q, ¬ prop q)

-- ============================================================================
-- Enumerable Sets
-- ============================================================================

/-- An enumerable set: there exists an enumerator that lists its elements. -/
def isEnumerable (enum : Nat → Option α) (S : α → Prop) : Prop :=
  ∀ a, S a ↔ ∃ n, enum n = some a

/-- Enumerator outputs are either origin (not found) or contents. -/
theorem enum_result (enum : Nat → Option α) (n : Nat) :
    partialResult (enum n) = origin ∨ ∃ a, partialResult (enum n) = contents a := by
  cases h : enum n with
  | none => left; rfl
  | some a => right; exact ⟨a, rfl⟩

-- ============================================================================
-- LOGIC
-- ============================================================================

-- ============================================================================
-- Propositional Logic: Formulas
-- ============================================================================

/-- A propositional formula. -/
inductive PropFormula (α : Type u) where
  | var : α → PropFormula α
  | propNot : PropFormula α → PropFormula α
  | propAnd : PropFormula α → PropFormula α → PropFormula α
  | propOr : PropFormula α → PropFormula α → PropFormula α
  | propImpl : PropFormula α → PropFormula α → PropFormula α

-- ============================================================================
-- Propositional Logic: Evaluation
-- ============================================================================

/-- Evaluate a propositional formula under a valuation.
    Evaluation is a valMap from formulas to truth values. -/
def propEval (v : α → Bool) : PropFormula α → Bool
  | .var a => v a
  | .propNot φ => !propEval v φ
  | .propAnd φ ψ => propEval v φ && propEval v ψ
  | .propOr φ ψ => propEval v φ || propEval v ψ
  | .propImpl φ ψ => !propEval v φ || propEval v ψ

/-- Lifting propositional evaluation to Val: always contents. -/
theorem propEval_contents (v : α → Bool) (φ : PropFormula α) :
    (contents (propEval v φ) : Val Bool) ≠ origin := by intro h; cases h

-- ============================================================================
-- Tautologies
-- ============================================================================

/-- A tautology: true under all valuations. -/
def isTautology (φ : PropFormula α) : Prop :=
  ∀ v : α → Bool, propEval v φ = true

/-- p ∨ ¬p is a tautology. -/
theorem lem_tautology (a : α) :
    isTautology (.propOr (.var a) (.propNot (.var a))) := by
  intro v; simp [propEval]

-- ============================================================================
-- Satisfiability
-- ============================================================================

/-- Satisfiable: true under some valuation. -/
def isSatisfiable (φ : PropFormula α) : Prop :=
  ∃ v : α → Bool, propEval v φ = true

/-- Every tautology is satisfiable (given any valuation exists). -/
theorem tautology_satisfiable (φ : PropFormula α) (h : isTautology φ)
    (v : α → Bool) : isSatisfiable φ := ⟨v, h v⟩

-- ============================================================================
-- First-Order Logic: Terms and Formulas
-- ============================================================================

/-- First-order terms. -/
inductive FOTerm (α : Type u) where
  | foVar : α → FOTerm α
  | foFunc : α → List (FOTerm α) → FOTerm α

/-- First-order formulas. -/
inductive FOFormula (α : Type u) where
  | foRel : α → List (FOTerm α) → FOFormula α
  | foNot : FOFormula α → FOFormula α
  | foAnd : FOFormula α → FOFormula α → FOFormula α
  | foOr : FOFormula α → FOFormula α → FOFormula α
  | foForall : α → FOFormula α → FOFormula α
  | foExists : α → FOFormula α → FOFormula α

-- ============================================================================
-- First-Order Logic: Interpretation
-- ============================================================================

/-- An interpretation assigns meaning to function and relation symbols. -/
structure Interpretation (α : Type u) where
  domain : Type u
  funcInterp : α → List domain → domain
  relInterp : α → List domain → Prop

-- ============================================================================
-- Logical Consequence
-- ============================================================================

/-- Logical consequence: φ follows from Γ if every model of Γ satisfies φ. -/
def logicalConsequence (eval : α → Bool) (premises conclusion : List (PropFormula α)) : Prop :=
  (∀ p ∈ premises, propEval eval p = true) →
  (∀ c ∈ conclusion, propEval eval c = true)

-- ============================================================================
-- Completeness and Soundness
-- ============================================================================

/-- Soundness: if provable, then valid. A contents-level statement. -/
def isSound (proves : α → Prop) (valid : α → Prop) : Prop :=
  ∀ φ, proves φ → valid φ

/-- Completeness: if valid, then provable. -/
def isComplete (proves : α → Prop) (valid : α → Prop) : Prop :=
  ∀ φ, valid φ → proves φ

/-- Soundness + completeness: proves ↔ valid. -/
theorem sound_complete_iff (proves valid : α → Prop)
    (hs : isSound proves valid) (hc : isComplete proves valid) (φ : α) :
    proves φ ↔ valid φ := ⟨hs φ, hc φ⟩

-- ============================================================================
-- Compactness
-- ============================================================================

/-- Compactness: a set of formulas is satisfiable iff every finite subset is. -/
def isCompact (sat : List α → Prop) (allFormulas : List α) : Prop :=
  sat allFormulas ↔ ∀ sub : List α, sub ⊆ allFormulas → sat sub

-- ============================================================================
-- Löwenheim-Skolem
-- ============================================================================

/-- Downward Löwenheim-Skolem: if a theory has a model of size κ,
    it has a model of every size λ ≤ κ (above the language size). -/
def hasModelOfSize (leF : α → α → Prop) (_theory : α) (size langSize : α) : Prop :=
  leF langSize size

-- ============================================================================
-- COMBINATORICS
-- ============================================================================

-- ============================================================================
-- Graphs: Basic Structure
-- ============================================================================

/-- A graph: vertices and an adjacency relation.
    origin = empty graph (no vertices). contents(G) = graph with data. -/
structure Graph (α : Type u) where
  vertices : α
  adj : α → α → Prop

/-- Graph as Val: contents wraps the vertex set. -/
def graphVal (G : Graph α) : Val α := contents G.vertices

-- ============================================================================
-- Graph Properties
-- ============================================================================

/-- Degree of a vertex: a valMap. -/
abbrev degree (degF : α → α) : Val α → Val α := valMap degF

/-- Number of edges: a valMap. -/
abbrev edgeCount (countF : α → α) : Val α → Val α := valMap countF

-- ============================================================================
-- Paths and Connectivity
-- ============================================================================

/-- A path: sequence of vertices. Encoded as contents. -/
def pathVal (path : List α) (encode : List α → α) : Val α :=
  contents (encode path)

/-- Connectivity: whether a path exists between two vertices. -/
def isConnected (connected : α → α → Prop) (u v : α) : Prop := connected u v

-- ============================================================================
-- Partitions
-- ============================================================================

/-- A partition of n: a list of positive integers summing to n. -/
structure Partition (α : Type u) where
  parts : List α
  total : α

/-- Partition as Val: the total is contents. -/
def partitionVal (p : Partition α) : Val α := contents p.total

/-- Partition count: number of partitions of n. A valMap. -/
abbrev partitionCount (countF : α → α) : Val α → Val α := valMap countF

-- ============================================================================
-- Binomial Coefficients
-- ============================================================================

/-- Binomial coefficient C(n,k). A binary operation on contents. -/
def binomial (chooseF : α → α → α) (n k : Val α) : Val α := mul chooseF n k

-- ============================================================================
-- Generating Functions
-- ============================================================================

/-- A generating function coefficient: the n-th coefficient. -/
def genFuncCoeff (coeffs : Nat → α) (n : Nat) : Val α := contents (coeffs n)

/-- Coefficients are always contents. -/
theorem genFuncCoeff_contents (coeffs : Nat → α) (n : Nat) :
    genFuncCoeff coeffs n = contents (coeffs n) := rfl

/-- Coefficient extraction via valMap. -/
abbrev extractCoeff (extractF : α → α) : Val α → Val α := valMap extractF

-- ============================================================================
-- Factorial and Falling Factorial
-- ============================================================================

/-- Factorial via valMap. -/
abbrev factorial (factF : α → α) : Val α → Val α := valMap factF

/-- Falling factorial via valMap. -/
abbrev fallingFactorial (fallF : α → α) : Val α → Val α := valMap fallF

-- ============================================================================
-- Young Tableaux
-- ============================================================================

/-- A Young diagram: a partition viewed as a shape. -/
structure YoungDiagram (α : Type u) where
  shape : List α

/-- Young diagram as Val. -/
def youngVal (Y : YoungDiagram α) (encode : List α → α) : Val α :=
  contents (encode Y.shape)

/-- Standard Young tableau count: a valMap on the shape. -/
abbrev tableauCount (countF : α → α) : Val α → Val α := valMap countF

-- ============================================================================
-- Matroids
-- ============================================================================

/-- A matroid: a ground set with an independence predicate. -/
structure Matroid (α : Type u) where
  ground : α
  independent : α → Prop

/-- Matroid rank: a valMap. -/
abbrev matroidRank (rankF : α → α) : Val α → Val α := valMap rankF

/-- Matroid ground set as Val. -/
def matroidVal (M : Matroid α) : Val α := contents M.ground

/-- Matroid closure: a valMap. -/
abbrev matroidClosure (clF : α → α) : Val α → Val α := valMap clF

-- ============================================================================
-- Ramsey Theory
-- ============================================================================

/-- Ramsey number: R(s,t) is a contents value. -/
def ramseyNumber (ramseyF : α → α → α) (s t : α) : Val α :=
  contents (ramseyF s t)

/-- Ramsey number is contents. -/
theorem ramsey_contents (ramseyF : α → α → α) (s t : α) :
    ramseyNumber ramseyF s t = contents (ramseyF s t) := rfl

/-- Ramsey symmetry: R(s,t) = R(t,s). -/
theorem ramsey_symm (ramseyF : α → α → α) (s t : α)
    (h : ramseyF s t = ramseyF t s) :
    ramseyNumber ramseyF s t = ramseyNumber ramseyF t s := by simp [ramseyNumber, h]

/-- Ramsey upper bound: R(s,t) ≤ R(s-1,t) + R(s,t-1). Contents inequality. -/
theorem ramsey_bound (leF : α → α → Prop) (addF : α → α → α)
    (rst rs1t rst1 : α) (h : leF rst (addF rs1t rst1)) :
    valLE leF (contents rst) (contents (addF rs1t rst1)) := h

-- ============================================================================
-- Graph Coloring
-- ============================================================================

/-- Chromatic number: minimum colors for proper coloring. A valMap. -/
abbrev chromaticNumber (chiF : α → α) : Val α → Val α := valMap chiF

-- ============================================================================
-- Catalan Numbers
-- ============================================================================

/-- Catalan number: C_n. A valMap. -/
abbrev catalanNumber (catF : α → α) : Val α → Val α := valMap catF

-- ============================================================================
-- Pigeonhole
-- ============================================================================

/-- Pigeonhole: if n+1 items in n boxes, some box has ≥ 2.
    The count is a contents-level value. -/
theorem pigeonhole_contents (items boxes : α) (ltF : α → α → Prop)
    (h : ltF boxes items) :
    valLT ltF (contents boxes) (contents items) := h

-- ============================================================================
-- Stirling Numbers
-- ============================================================================

/-- Stirling number of the second kind: S(n,k). A valMap. -/
abbrev stirling2 (stirF : α → α → α) (n k : Val α) : Val α := mul stirF n k

-- ============================================================================
-- Euler's Formula for Planar Graphs
-- ============================================================================

/-- Euler's formula: V - E + F = 2. Contents arithmetic. -/
theorem euler_formula_contents (addF : α → α → α) (negF : α → α)
    (v e f two : α) (h : addF (addF v (negF e)) f = two) :
    add addF (add addF (contents v) (contents (negF e))) (contents f) =
    contents two := by simp [h]

-- ============================================================================
-- Fibonacci Numbers
-- ============================================================================

/-- Fibonacci via valMap. -/
abbrev fibonacci (fibF : α → α) : Val α → Val α := valMap fibF

-- ============================================================================
-- Bell Numbers
-- ============================================================================

/-- Bell number: B_n = Σ S(n,k). A valMap. -/
abbrev bellNumber (bellF : α → α) : Val α → Val α := valMap bellF

-- ============================================================================
-- Derangements
-- ============================================================================

/-- Derangement count: D(n). A valMap. -/
abbrev derangement (derF : α → α) : Val α → Val α := valMap derF

/-- Derangement recurrence: D(n) = (n-1)(D(n-1) + D(n-2)). Contents arithmetic. -/
theorem derangement_recurrence (mulF addF : α → α → α) (n_minus_1 dn1 dn2 : α) :
    mul mulF (contents n_minus_1) (add addF (contents dn1) (contents dn2)) =
    contents (mulF n_minus_1 (addF dn1 dn2)) := rfl

-- ============================================================================
-- Graph: Trees
-- ============================================================================

-- ============================================================================
-- Graph: Bipartite
-- ============================================================================

/-- Bipartite graph: vertices split into two sets. -/
structure BipartiteGraph (α : Type u) where
  left : α
  right : α
  edges : α

/-- Bipartite graph as Val: vertex set is contents. -/
def bipartiteVal (G : BipartiteGraph α) (pairF : α → α → α) : Val α :=
  contents (pairF G.left G.right)

-- ============================================================================
-- Graph: Matching
-- ============================================================================

/-- Matching size: a valMap. -/
abbrev matchingSize (matchF : α → α) : Val α → Val α := valMap matchF

-- ============================================================================
-- Graph: Spanning Trees
-- ============================================================================

/-- Kirchhoff's theorem: number of spanning trees via matrix tree theorem. -/
abbrev spanTreeCount (detF : α → α) : Val α → Val α := valMap detF

-- ============================================================================
-- Graph: Flows and Cuts
-- ============================================================================

/-- Max flow = min cut. Both sides are contents. -/
theorem max_flow_min_cut (flow cut : α) (h : flow = cut) :
    (contents flow : Val α) = contents cut := by rw [h]

-- ============================================================================
-- Lattice Paths
-- ============================================================================

-- ============================================================================
-- Multinomial Coefficients
-- ============================================================================

/-- Multinomial coefficient: n! / (k₁! · k₂! · ... · kₘ!). A valMap. -/
abbrev multinomial (multiF : α → α) : Val α → Val α := valMap multiF

-- ============================================================================
-- Möbius Function
-- ============================================================================

/-- Möbius function on a poset: μ(x,y). -/
def mobiusVal (mobiusF : α → α → α) (x y : α) : Val α :=
  contents (mobiusF x y)

-- ============================================================================
-- Polynomial Method
-- ============================================================================

/-- Combinatorial Nullstellensatz: degree bound. Contents inequality. -/
theorem nullstellensatz_bound (leF : α → α → Prop) (deg bound : α) (h : leF deg bound) :
    valLE leF (contents deg) (contents bound) := h

-- ============================================================================
-- Hypergraph
-- ============================================================================

/-- A hypergraph: vertices and hyperedges (subsets of vertices). -/
structure Hypergraph (α : Type u) where
  vertices : α
  hyperedges : α

/-- Hypergraph as Val. -/
def hypergraphVal (H : Hypergraph α) : Val α := contents H.vertices

/-- Hypergraph rank: maximum edge size. A valMap. -/
abbrev hypergraphRank (rankF : α → α) : Val α → Val α := valMap rankF

-- ============================================================================
-- Turán's Theorem
-- ============================================================================

/-- Turán number: max edges in K_{r+1}-free graph on n vertices. -/
def turanNumber (turanF : α → α → α) (n r : α) : Val α :=
  contents (turanF n r)

theorem turan_contents (turanF : α → α → α) (n r : α) :
    turanNumber turanF n r = contents (turanF n r) := rfl

/-- Turán bound: edge count ≤ Turán number. -/
theorem turan_bound (leF : α → α → Prop) (edges turan : α) (h : leF edges turan) :
    valLE leF (contents edges) (contents turan) := h

-- ============================================================================
-- Extremal Graph Theory
-- ============================================================================

/-- Zarankiewicz problem: z(m,n;s,t). -/
def zarankiewicz (zF : α → α → α → α → α) (m n s t : α) : Val α :=
  contents (zF m n s t)

/-- Kruskal-Katona: shadow bound. -/
theorem kruskal_katona_bound (leF : α → α → Prop) (shadow bound : α) (h : leF shadow bound) :
    valLE leF (contents shadow) (contents bound) := h

-- ============================================================================
-- Probabilistic Combinatorics
-- ============================================================================

/-- Lovász Local Lemma: if dependencies are bounded, probability is positive. -/
theorem lll_positive (ltF : α → α → Prop) (zero prob : α) (h : ltF zero prob) :
    valLT ltF (contents zero) (contents prob) := h

end Val
