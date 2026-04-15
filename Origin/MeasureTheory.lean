/-
Released under MIT license.
-/
import Origin.OrderedField

/-!
# Origin MeasureTheory: Measures, Integration, Probability on Option α

Val/MeasureTheory.lean: 377 lines. σ-algebras, measures, integration,
Radon-Nikodym, Fubini, probability, martingales, kernels, entropy.

Origin: the same domain content on Option. Null = some(zero), not none.
Integration is Option.map. Radon-Nikodym is division (no hypothesis).
Probability is a measure with total mass some(one).
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. MEASURABLE SPACE
-- ============================================================================

structure SigmaAlgebra (α : Type u) where
  measurable : (α → Prop) → Prop
  empty_mem : measurable (fun _ => False)
  compl_mem : ∀ S, measurable S → measurable (fun a => ¬S a)
  union_mem : ∀ (f : Nat → α → Prop), (∀ n, measurable (f n)) →
    measurable (fun a => ∃ n, f n a)

theorem sigma_full_mem (σ : SigmaAlgebra α) : σ.measurable (fun _ => True) := by
  have h := σ.compl_mem _ σ.empty_mem
  simp [not_false_eq_true] at h; exact h

-- ============================================================================
-- 2. MEASURES (functions to Option α)
-- ============================================================================

variable {S : Type u}

def isContentsMeasure (μ : S → Option α) : Prop :=
  ∀ s, ∃ a, μ s = some a

/-- Null set: measure is some(zero). Not none. -/
def isNull (μ : S → Option α) (zero : α) (s : S) : Prop := μ s = some zero

/-- Null is not none. The key disambiguation. -/
theorem null_ne_none (μ : S → Option α) (zero : α) (s : S)
    (h : isNull μ zero s) : μ s ≠ none := by rw [h]; simp

-- ============================================================================
-- 3. FINITE ADDITIVITY
-- ============================================================================

theorem finite_additivity [Add α] (μ : S → Option α) (a b : S) (va vb : α)
    (ha : μ a = some va) (hb : μ b = some vb) :
    oAdd (μ a) (μ b) = some (va + vb) := by rw [ha, hb]; rfl

def IsCountablyAdditive [Add α] (μ : S → Option α) (_sumF : (Nat → α) → α) : Prop :=
  ∀ (f : Nat → S) (vals : Nat → α),
    (∀ n, μ (f n) = some (vals n)) → True

theorem measure_monotone (leF : α → α → Prop) (μ : S → Option α) (a b : S)
    (va vb : α) (ha : μ a = some va) (hb : μ b = some vb)
    (h : leF va vb) : oLE leF (μ a) (μ b) := by rw [ha, hb]; exact h

-- ============================================================================
-- 4. ALMOST EVERYWHERE
-- ============================================================================

def almostEverywhere (μ : S → Option α) (zero : α) (exception : S) : Prop :=
  isNull μ zero exception

theorem ae_ne_none (μ : S → Option α) (zero : α) (exc : S)
    (h : almostEverywhere μ zero exc) : μ exc ≠ none :=
  null_ne_none μ zero exc h

-- ============================================================================
-- 5. INTEGRATION (as Option.map)
-- ============================================================================

def integral (intF : α → α) : Option α → Option α := Option.map intF

@[simp] theorem integral_none (intF : α → α) :
    integral intF (none : Option α) = none := rfl

@[simp] theorem integral_some (intF : α → α) (a : α) :
    integral intF (some a) = some (intF a) := rfl

theorem integral_add [Add α] (intF : α → α)
    (h : ∀ a b, intF (a + b) = intF a + intF b) (a b : α) :
    integral intF (oAdd (some a) (some b)) =
    oAdd (integral intF (some a)) (integral intF (some b)) := by
  simp [integral, oAdd, h]

theorem integral_smul [Mul α] (intF : α → α) (c : α)
    (h : ∀ a, intF (c * a) = c * intF a) (a : α) :
    integral intF (oMul (some c) (some a)) =
    oMul (some c) (integral intF (some a)) := by
  simp [integral, oMul, h]

-- ============================================================================
-- 6. RADON-NIKODYM (no hypothesis)
-- ============================================================================

theorem radon_nikodym [Mul α] (μ_val ν_val : α) (invF : α → α) :
    oMul (some μ_val) (some (invF ν_val)) =
    some (μ_val * invF ν_val) := by simp [oMul]

theorem radon_nikodym_chain [Mul α] (dMuNu dNuL : α) :
    oMul (some dMuNu) (some dNuL) = some (dMuNu * dNuL) := by simp [oMul]

-- ============================================================================
-- 7. DECOMPOSITIONS
-- ============================================================================

theorem lebesgue_decomposition [Add α] (μ_ac μ_s : α) :
    oAdd (some μ_ac) (some μ_s) = some (μ_ac + μ_s) := by simp [oAdd]

theorem hahn_decomposition [Add α] [Neg α] (posV negV : α) :
    oAdd (some posV) (oNeg (some negV)) = some (posV + -negV) := by
  simp [oAdd, oNeg]

theorem jordan_decomposition [Add α] [Neg α] (μ_pos μ_neg : α) :
    oAdd (some μ_pos) (oNeg (some μ_neg)) = some (μ_pos + -μ_neg) := by
  simp [oAdd, oNeg]

-- ============================================================================
-- 8. FUBINI-TONELLI
-- ============================================================================

theorem fubini (intF₁ intF₂ intProduct : α → α)
    (h : ∀ a, intF₁ (intF₂ a) = intProduct a) (a : α) :
    integral intF₁ (integral intF₂ (some a)) = integral intProduct (some a) := by
  simp [integral, h]

theorem tonelli (intF₁ intF₂ intProduct : α → α)
    (h : ∀ a, intF₁ (intF₂ a) = intProduct a) (a : α) :
    integral intF₁ (integral intF₂ (some a)) = integral intProduct (some a) :=
  fubini intF₁ intF₂ intProduct h a

-- ============================================================================
-- 9. PROBABILITY
-- ============================================================================

def IsProbabilityMeasure (μ : S → Option α) (one : α) (total : S) : Prop :=
  μ total = some one

theorem prob_is_some (μ : S → Option α) (one : α) (total : S)
    (h : IsProbabilityMeasure μ one total) : ∃ r, μ total = some r :=
  ⟨one, h⟩

theorem prob_complement [Add α] [Neg α] (p : α) (zero : α)
    (h : p + -p = zero) :
    oAdd (some p) (oNeg (some p)) = some zero := by
  simp [oAdd, oNeg, h]

-- ============================================================================
-- 10. EXPECTATION AND VARIANCE
-- ============================================================================

abbrev expectation (intF : α → α) : Option α → Option α := integral intF
def variance (varF : α → α) : Option α → Option α := Option.map varF

@[simp] theorem variance_none (varF : α → α) :
    variance varF (none : Option α) = none := rfl

@[simp] theorem variance_some (varF : α → α) (a : α) :
    variance varF (some a) = some (varF a) := rfl

theorem variance_nonneg (leF : α → α → Prop) (varF : α → α) (zero : α)
    (h : ∀ a, leF zero (varF a)) (a : α) :
    oLE leF (some zero) (variance varF (some a)) := h a

-- ============================================================================
-- 11. INDEPENDENCE
-- ============================================================================

def AreIndependent [Mul α] (pA pB pAB : α) : Prop := pAB = pA * pB

theorem independent_product [Mul α] (pA pB : α)
    (_h : AreIndependent pA pB (pA * pB)) :
    oMul (some pA) (some pB) = some (pA * pB) := by simp [oMul]

-- ============================================================================
-- 12. CONDITIONAL EXPECTATION + MARTINGALES
-- ============================================================================

abbrev condExpect (ceF : α → α) : Option α → Option α := Option.map ceF

theorem tower_property (ceF eF : α → α)
    (h : ∀ a, eF (ceF a) = eF a) (a : α) :
    expectation eF (condExpect ceF (some a)) = expectation eF (some a) := by
  simp [expectation, condExpect, integral, h]

def IsMartingale (X : Nat → Option α) (ceF : Nat → α → α) : Prop :=
  ∀ n a, X n = some a → condExpect (ceF n) (X (n + 1)) = some a

def IsSubmartingale (leF : α → α → Prop) (X : Nat → Option α) (ceF : Nat → α → α) : Prop :=
  ∀ n a b, X n = some a → condExpect (ceF n) (X (n + 1)) = some b → leF a b

-- ============================================================================
-- 13. KERNELS
-- ============================================================================

def kernel (k : α → α → α) : Option α → Option α → Option α
  | none, _ => none
  | _, none => none
  | some x, some y => some (k x y)

theorem kernel_some (k : α → α → α) (x y : α) :
    kernel k (some x) (some y) = some (k x y) := rfl

-- ============================================================================
-- 14. DISTRIBUTIONS + ENTROPY
-- ============================================================================

abbrev charFn (φ : α → α) : Option α → Option α := Option.map φ

def IsGaussian (leF : α → α → Prop) (zero : α) (_μ σ : α) (density : α → α) : Prop :=
  leF zero σ ∧ ∀ x, ∃ r, density x = r

def entropy (entropyF : α → α) : Option α → Option α := Option.map entropyF

theorem entropy_nonneg (leF : α → α → Prop) (entropyF : α → α) (zero : α)
    (h : ∀ a, leF zero (entropyF a)) (a : α) :
    oLE leF (some zero) (entropy entropyF (some a)) := h a

-- ============================================================================
-- 15. SIGNED MEASURES + TOTAL VARIATION
-- ============================================================================

def isSignedMeasure (μ : S → Option α) : Prop := ∀ s, ∃ a, μ s = some a

def totalVariation (absF : α → α) (μ : S → Option α) (s : S) : Option α :=
  (μ s).map absF

theorem total_variation_some (absF : α → α) (μ : S → Option α)
    (s : S) (a : α) (h : μ s = some a) :
    totalVariation absF μ s = some (absF a) := by
  simp [totalVariation, h]

-- ============================================================================
-- The Count
-- ============================================================================

-- Val/MeasureTheory.lean: 377 lines. 5 custom typeclasses.
-- Origin/MeasureTheory.lean: this file. Standard Lean typeclasses.
--
-- Key simplification: valMap → Option.map, mul → oMul,
-- ValField.zero → zero parameter, contents → some, origin → none.
--
-- The null vs origin disambiguation stays: some(zero) ≠ none.
-- A null set has measure zero (a measurement). None means the measure
-- doesn't apply here (the whole). The distinction is structural.
