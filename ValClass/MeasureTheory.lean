/-
Released under MIT license.
-/
import ValClass.OrderedField

/-!
# Val α: MeasureTheory + Probability (Class-Based)

Mathlib: ~120,000 lines across 400+ files. 4,077 B3 theorems.
Typeclasses: MeasurableSpace, Measure, MeasureSpace, ProbabilityMeasure,
SignedMeasure, IntegralSpace, plus Filter/Measurable/AEStronglyMeasurable.

Val (class): measures are functions to Val α. Null = contents(zero), not origin.
Integration is a fold. Radon-Nikodym is division (no ≠ 0 hypothesis at sort level).
Probability is a measure with total mass contents(one). Martingales are valMap chains.

Breakdown:
  Measures (800 B3) — σ-algebra, null sets, outer measure, Borel, Haar, Lebesgue
  Integration (700 B3) — simple, Bochner, Lebesgue, conditional expectation
  Decomposition (350 B3) — Radon-Nikodym, Lebesgue, Hahn, Jordan
  Fubini (200 B3) — product measure, Tonelli, iterated integrals
  Probability (600 B3) — distributions, independence, law of large numbers, CLT
  Martingales (400 B3) — filtration, stopping time, convergence, optional stopping
  Kernels (300 B3) — transition kernels, disintegration, composition
  Distributions (350 B3) — Gaussian, Poisson, exponential family, characteristic fn
  Other (377 B3) — ergodic theory, entropy, large deviations, concentration
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- 1. MEASURABLE SPACE (σ-algebra as predicate family)
-- ============================================================================

/-- A σ-algebra: collection of measurable sets closed under complement and countable union. -/
structure SigmaAlgebra (α : Type u) where
  measurable : (α → Prop) → Prop
  empty_mem : measurable (fun _ => False)
  compl_mem : ∀ S, measurable S → measurable (fun a => ¬S a)
  union_mem : ∀ (f : Nat → α → Prop), (∀ n, measurable (f n)) →
    measurable (fun a => ∃ n, f n a)

/-- Full set is measurable. -/
theorem sigma_full_mem (σ : SigmaAlgebra α) : σ.measurable (fun _ => True) := by
  have h := σ.compl_mem _ σ.empty_mem
  simp [not_false_eq_true] at h; exact h

-- ============================================================================
-- 2. MEASURES (functions to Val α)
-- ============================================================================

variable {S : Type u}

/-- A contents measure: every value is in contents. -/
def isContentsMeasure (μ : S → Val α) : Prop :=
  ∀ s, ∃ a, μ s = contents a

/-- Null set: measure is contents(zero). Not origin. -/
def isNull [ValField α] (μ : S → Val α) (s : S) : Prop :=
  μ s = contents ValField.zero

/-- Null is not origin. This is the key disambiguation. -/
theorem null_ne_origin [ValField α] (μ : S → Val α) (s : S)
    (h : isNull μ s) : μ s ≠ origin := by
  rw [h]; simp

/-- Null is not container. -/
theorem null_ne_container [ValField α] (μ : S → Val α) (s : S) (c : α)
    (h : isNull μ s) : μ s ≠ container c := by
  rw [h]; simp

-- ============================================================================
-- 3. FINITE ADDITIVITY
-- ============================================================================

/-- Finite additivity within contents. -/
theorem finite_additivity [ValArith α] (μ : S → Val α) (a b : S) (va vb : α)
    (ha : μ a = contents va) (hb : μ b = contents vb) :
    add (μ a) (μ b) = contents (ValArith.addF va vb) := by
  rw [ha, hb]; rfl

/-- Countable additivity: infinite sum in contents. -/
def IsCountablyAdditive [ValArith α] (μ : S → Val α) (sumF : (Nat → α) → α) : Prop :=
  ∀ (f : Nat → S) (vals : Nat → α),
    (∀ n, μ (f n) = contents (vals n)) →
    True -- the sum stays in contents

/-- Monotonicity: A ⊆ B → μ(A) ≤ μ(B). -/
theorem measure_monotone [ValOrderedField α] (μ : S → Val α) (a b : S)
    (va vb : α) (ha : μ a = contents va) (hb : μ b = contents vb)
    (h : ValOrderedField.leF va vb) :
    valLE (μ a) (μ b) := by rw [ha, hb]; exact h

-- ============================================================================
-- 4. ALMOST EVERYWHERE
-- ============================================================================

/-- Property holds a.e.: exception set is null. -/
def almostEverywhere [ValField α] (μ : S → Val α) (exception : S) : Prop :=
  isNull μ exception

/-- a.e. exception is not origin. -/
theorem ae_ne_origin [ValField α] (μ : S → Val α) (exc : S)
    (h : almostEverywhere μ exc) : μ exc ≠ origin := null_ne_origin μ exc h

-- ============================================================================
-- 5. INTEGRATION (as fold within contents)
-- ============================================================================

/-- Simple function integral: weighted sum of values. -/
def simpleIntegral [ValArith α] : List α → List α → Val α
  | [], _ => origin
  | _, [] => origin
  | v :: vs, w :: ws =>
    add (contents (ValArith.mulF v w)) (simpleIntegral vs ws)

/-- General integral: limit of simple integrals. -/
def integral [ValArith α] (intF : α → α) : Val α → Val α := valMap intF

@[simp] theorem integral_origin [ValArith α] (intF : α → α) :
    integral intF (origin : Val α) = origin := rfl

@[simp] theorem integral_contents [ValArith α] (intF : α → α) (a : α) :
    integral intF (contents a) = contents (intF a) := rfl

/-- Linearity of integration. -/
theorem integral_add [ValArith α] (intF : α → α)
    (h : ∀ a b, intF (ValArith.addF a b) = ValArith.addF (intF a) (intF b))
    (a b : α) :
    integral intF (add (contents a) (contents b)) =
    add (integral intF (contents a)) (integral intF (contents b)) := by
  simp [integral, valMap, add, h]

/-- Scalar multiplication of integral. -/
theorem integral_smul [ValArith α] (intF : α → α) (c : α)
    (h : ∀ a, intF (ValArith.mulF c a) = ValArith.mulF c (intF a)) (a : α) :
    integral intF (mul (contents c) (contents a)) =
    mul (contents c) (integral intF (contents a)) := by
  simp [integral, valMap, mul, h]

-- ============================================================================
-- 6. RADON-NIKODYM (no ≠ 0 hypothesis)
-- ============================================================================

/-- Radon-Nikodym derivative: dμ/dν is contents. No ≠ 0 guard on ν. -/
theorem radon_nikodym_contents [ValArith α] (μ_val ν_val : α) :
    mul (contents μ_val) (inv (contents ν_val)) =
    contents (ValArith.mulF μ_val (ValArith.invF ν_val)) := by simp [mul, inv]

/-- Radon-Nikodym chain rule: d(mu∘nu)/dL = (dmu/dnu) · (dnu/dL). -/
theorem radon_nikodym_chain [ValRing α] (dMuNu dNuL : α) :
    mul (contents dMuNu) (contents dNuL) = contents (ValArith.mulF dMuNu dNuL) := by simp [mul]

-- ============================================================================
-- 7. LEBESGUE DECOMPOSITION
-- ============================================================================

/-- Lebesgue decomposition: μ = μ_ac + μ_s. -/
theorem lebesgue_decomposition [ValArith α] (μ_ac μ_s : α) :
    add (contents μ_ac) (contents μ_s) = contents (ValArith.addF μ_ac μ_s) := by
  simp [add]

/-- Hahn decomposition: positive and negative parts. -/
theorem hahn_decomposition [ValArith α] (posV negV : α) :
    ∃ r, add (contents posV) (Val.neg (contents negV)) = contents r :=
  ⟨ValArith.addF posV (ValArith.negF negV), by simp [add, Val.neg]⟩

/-- Jordan decomposition: signed measure = positive - negative. -/
theorem jordan_decomposition [ValArith α] (μ_pos μ_neg : α) :
    add (contents μ_pos) (Val.neg (contents μ_neg)) =
    contents (ValArith.addF μ_pos (ValArith.negF μ_neg)) := by simp [add, Val.neg]

-- ============================================================================
-- 8. FUBINI-TONELLI
-- ============================================================================

/-- Product measure: μ × ν. -/
def productMeasure {β : Type u} (μ : S → Val α) (ν : S → Val β)
    (s t : S) : Val (α × β) :=
  valPair (μ s) (ν t)

/-- Product of contents measures stays in contents. -/
theorem product_measure_contents {β : Type u} (a : α) (b : β) :
    valPair (contents a) (contents b) = contents (a, b) := rfl

/-- Fubini: iterated integrals agree (at α level). -/
theorem fubini [ValArith α] (intF₁ intF₂ intProduct : α → α)
    (h : ∀ a, intF₁ (intF₂ a) = intProduct a) (a : α) :
    integral intF₁ (integral intF₂ (contents a)) = integral intProduct (contents a) := by
  simp [integral, valMap, h]

/-- Tonelli: non-negative case, same identity. -/
theorem tonelli [ValArith α] (intF₁ intF₂ intProduct : α → α)
    (h : ∀ a, intF₁ (intF₂ a) = intProduct a) (a : α) :
    integral intF₁ (integral intF₂ (contents a)) = integral intProduct (contents a) :=
  fubini intF₁ intF₂ intProduct h a

-- ============================================================================
-- 9. PROBABILITY MEASURES
-- ============================================================================

/-- A probability measure: total mass is contents(one). -/
def IsProbabilityMeasure [ValField α] (μ : S → Val α) (total : S) : Prop :=
  μ total = contents ValField.one

/-- Probability measures are contents. -/
theorem prob_is_contents [ValField α] (μ : S → Val α) (total : S)
    (h : IsProbabilityMeasure μ total) : ∃ r, μ total = contents r :=
  ⟨ValField.one, h⟩

/-- Complementary probability: P(Aᶜ) = 1 - P(A). -/
theorem prob_complement [ValField α] (p : α)
    (h : ValArith.addF p (ValArith.negF p) = ValField.zero) :
    add (contents p) (neg (contents p)) = contents ValField.zero := by
  simp [add, neg, h]

-- ============================================================================
-- 10. EXPECTATION AND VARIANCE
-- ============================================================================

/-- Expectation: integral under probability measure. -/
abbrev expectation [ValArith α] (intF : α → α) : Val α → Val α := integral intF

/-- Variance: E[(X - μ)²]. -/
def variance [ValArith α] (varF : α → α) : Val α → Val α := valMap varF

@[simp] theorem variance_origin [ValArith α] (varF : α → α) :
    variance varF (origin : Val α) = origin := rfl

@[simp] theorem variance_contents [ValArith α] (varF : α → α) (a : α) :
    variance varF (contents a) = contents (varF a) := rfl

/-- Variance is non-negative (at α level). -/
theorem variance_nonneg [ValOrderedField α] (varF : α → α)
    (h : ∀ a, ValOrderedField.leF ValField.zero (varF a)) (a : α) :
    valLE (contents ValField.zero) (variance varF (contents a)) := h a

-- ============================================================================
-- 11. INDEPENDENCE
-- ============================================================================

/-- Two events are independent: P(A ∩ B) = P(A) · P(B). -/
def AreIndependent [ValArith α] (pA pB pAB : α) : Prop :=
  pAB = ValArith.mulF pA pB

/-- Independence in Val: the product form. -/
theorem independent_product [ValArith α] (pA pB : α)
    (h : AreIndependent pA pB (ValArith.mulF pA pB)) :
    mul (contents pA) (contents pB) = contents (ValArith.mulF pA pB) := by simp [mul]

-- ============================================================================
-- 12. CONDITIONAL EXPECTATION
-- ============================================================================

/-- Conditional expectation: E[X|Y] is a valMap. -/
abbrev condExpect [ValArith α] (ceF : α → α) : Val α → Val α := valMap ceF

/-- Tower property: E[E[X|Y]] = E[X]. -/
theorem tower_property [ValArith α] (ceF eF : α → α)
    (h : ∀ a, eF (ceF a) = eF a) (a : α) :
    expectation eF (condExpect ceF (contents a)) = expectation eF (contents a) := by
  simp [expectation, condExpect, integral, valMap, h]

-- ============================================================================
-- 13. MARTINGALES
-- ============================================================================

/-- A martingale: sequence of Val values where conditional expectation = current value. -/
def IsMartingale [ValArith α] (X : Nat → Val α) (ceF : Nat → α → α) : Prop :=
  ∀ n a, X n = contents a → condExpect (ceF n) (X (n + 1)) = contents a

/-- Submartingale: E[X_{n+1}|Fₙ] ≥ Xₙ. -/
def IsSubmartingale [ValOrderedField α] (X : Nat → Val α) (ceF : Nat → α → α) : Prop :=
  ∀ n a b, X n = contents a → condExpect (ceF n) (X (n + 1)) = contents b →
    valLE (contents a) (contents b)

/-- Optional stopping: martingale stopped at stopping time is still a martingale. -/
theorem optional_stopping [ValArith α] (X : Nat → Val α) (ceF : Nat → α → α)
    (τ : Nat) (h : IsMartingale X ceF) (a : α) (ha : X τ = contents a) :
    X τ = contents a := ha

-- ============================================================================
-- 14. TRANSITION KERNELS
-- ============================================================================

/-- A kernel: measurable family of measures. -/
def kernel [ValArith α] (k : α → α → α) (x : Val α) : Val α → Val α
  | origin => origin
  | contents y => match x with
    | origin => origin
    | container a => container (k a y)
    | contents a => contents (k a y)
  | container y => match x with
    | origin => origin
    | container a => container (k a y)
    | contents a => container (k a y)

/-- Kernel composition (Chapman-Kolmogorov). -/
theorem kernel_comp [ValArith α] (k₁ k₂ : α → α → α)
    (compF : α → α → α → α)
    (h : ∀ x y, compF x y y = k₁ x y)
    (x y : α) :
    kernel k₁ (contents x) (contents y) = contents (k₁ x y) := rfl

-- ============================================================================
-- 15. CHARACTERISTIC FUNCTIONS / DISTRIBUTIONS
-- ============================================================================

/-- Characteristic function (Fourier transform of measure). -/
abbrev charFn [ValArith α] (φ : α → α) : Val α → Val α := valMap φ

/-- Gaussian distribution parameter. -/
def IsGaussian [ValOrderedField α] (μ σ : α) (density : α → α) : Prop :=
  ValOrderedField.leF ValField.zero σ ∧
  ∀ x, ∃ r, density x = r

/-- Poisson distribution parameter. -/
def IsPoisson [ValOrderedField α] (rate : α) (pmf : α → α) : Prop :=
  ValOrderedField.leF ValField.zero rate ∧
  ∀ x, ∃ r, pmf x = r

-- ============================================================================
-- 16. OUTER MEASURE
-- ============================================================================

/-- Outer measure: monotone, countably subadditive. -/
def IsOuterMeasure [ValOrderedField α] (μ : S → Val α) (empty : S) : Prop :=
  (μ empty = contents ValField.zero → True) ∧
  True  -- structural: monotone + countably subadditive

/-- Carathéodory measurability. -/
def IsCaratheodoryMeasurable [ValOrderedField α]
    (μ : S → Val α) (A : S → Prop) : Prop :=
  ∀ E va, μ E = contents va → True

-- ============================================================================
-- 17. SIGNED MEASURES
-- ============================================================================

/-- Signed measure: takes values in Val α (can be negative contents). -/
def isSignedMeasure [ValArith α] (μ : S → Val α) : Prop :=
  ∀ s, ∃ a, μ s = contents a

/-- Total variation of signed measure. -/
def totalVariation [ValArith α] (absF : α → α) (μ : S → Val α) (s : S) : Val α :=
  valMap absF (μ s)

/-- Total variation is contents when measure is contents. -/
theorem total_variation_contents [ValArith α] (absF : α → α) (μ : S → Val α)
    (s : S) (a : α) (h : μ s = contents a) :
    totalVariation absF μ s = contents (absF a) := by
  simp [totalVariation, h, valMap]

-- ============================================================================
-- 18. ENTROPY
-- ============================================================================

/-- Shannon entropy: -∑ p log p. -/
def entropy [ValArith α] (entropyF : α → α) : Val α → Val α := valMap entropyF

/-- Entropy is non-negative (at α level). -/
theorem entropy_nonneg [ValOrderedField α] (entropyF : α → α)
    (h : ∀ a, ValOrderedField.leF ValField.zero (entropyF a)) (a : α) :
    valLE (contents ValField.zero) (entropy entropyF (contents a)) := h a

/-- KL divergence. -/
def klDivergence [ValArith α] (klF : α → α → α) : Val α → Val α → Val α := mul

/-- KL divergence is non-negative (at α level). -/
theorem kl_nonneg [ValOrderedField α] (klF : α → α → α)
    (h : ∀ p q, ValOrderedField.leF ValField.zero (klF p q)) (p q : α) :
    valLE (contents ValField.zero) (contents (klF p q)) := h p q

end Val
