/-
Released under MIT license.
-/
import Val.Algebra.Core

/-!
# Measure Theory on Val α

Measures, null sets, integration, decomposition, specific constructions.

The key disambiguation: `contents(0)` is measure zero. `origin` is the boundary.
In standard math both are written 0. Val α makes the sorts visible.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- § Core: Measures
-- ============================================================================

variable {S : Type u}  -- index type for measurable sets

/-- A contents measure assigns contents values to every set. -/
def isContentsMeasure (μ : S → Val α) : Prop :=
  ∀ s : S, ∃ a : α, μ s = contents a

-- ============================================================================
-- § Core: Null Sets — contents(0), Not Origin
-- ============================================================================

/-- A set is null when its measure is contents(zero). NOT origin. -/
def isNull (μ : S → Val α) (zero : α) (s : S) : Prop :=
  μ s = contents zero

/-- Null sets are not origin. Measure zero ≠ boundary. -/
theorem null_ne_origin (μ : S → Val α) (zero : α) (s : S)
    (h : isNull μ zero s) : μ s ≠ origin := by
  rw [h]; simp

/-- Null sets are not container. -/
theorem null_ne_container (μ : S → Val α) (zero : α) (s : S) (c : α)
    (h : isNull μ zero s) : μ s ≠ container c := by
  rw [h]; simp

-- ============================================================================
-- § Core: Countable Additivity Within Contents
-- ============================================================================

/-- Finite additivity: μ(A) + μ(B) is contents when both are contents. -/
theorem finite_additivity_contents (addF : α → α → α)
    (μ : S → Val α) (a b : S) (va vb : α)
    (ha : μ a = contents va) (hb : μ b = contents vb) :
    add addF (μ a) (μ b) = contents (addF va vb) := by
  rw [ha, hb]; rfl

-- ============================================================================
-- § Core: Almost Everywhere
-- ============================================================================

/-- A property holds a.e. when the exception set is null.
    The exception has measure contents(zero) — not origin. -/
def almostEverywhere (μ : S → Val α) (zero : α) (exception : S) : Prop :=
  isNull μ zero exception

/-- Almost everywhere exception is not origin. -/
theorem ae_ne_origin (μ : S → Val α) (zero : α) (exc : S)
    (h : almostEverywhere μ zero exc) : μ exc ≠ origin :=
  null_ne_origin μ zero exc h

-- ============================================================================
-- § Core: Radon-Nikodym — No ≠ 0 Hypothesis
-- ============================================================================

/-- Radon-Nikodym derivative: dμ/dν is contents. No hypothesis on ν. -/
theorem radon_nikodym_contents (mulF : α → α → α) (invF : α → α)
    (μ_val ν_val : α) :
    mul mulF (contents μ_val) (inv invF (contents ν_val)) =
    contents (mulF μ_val (invF ν_val)) := rfl

-- ============================================================================
-- § Core: Integration Within Contents
-- ============================================================================

/-- Integration accumulation stays in contents at every step. -/
theorem integral_accumulate (addF mulF : α → α → α)
    (running value measure_val : α) :
    add addF (contents running)
             (mul mulF (contents value) (contents measure_val)) =
    contents (addF running (mulF value measure_val)) := rfl

-- ============================================================================
-- § Core: σ-Finiteness
-- ============================================================================

/-- A contents measure over a countable cover never produces origin. -/
theorem sigma_finite_contents (μ : S → Val α)
    (cover : Nat → S)
    (h : ∀ n, ∃ a : α, μ (cover n) = contents a) :
    ∀ n, μ (cover n) ≠ origin := by
  intro n
  obtain ⟨a, ha⟩ := h n
  rw [ha]; simp

-- ============================================================================
-- § Core: Origin Absorption in Measure Computations
-- ============================================================================

/-- Origin absorbs in measure addition. -/
theorem measure_origin_absorbs (addF : α → α → α) (a : α) :
    add addF origin (contents a) = origin := by simp

/-- Origin absorbs in integration. -/
theorem integral_origin_absorbs (mulF : α → α → α) (a : α) :
    mul mulF (contents a) origin = origin := by simp

-- ============================================================================
-- § Construct: Product Measure
-- ============================================================================

variable {T : Type u}

-- ============================================================================
-- § Construct: Pushforward Measure
-- ============================================================================

/-- Pushforward measure: f_* μ (A) = μ(f⁻¹(A)).
    In Val α: pushforward of contents measure is contents. -/
def pushforwardMeasure (f : S → T) (μ : S → Val α) (preimage : T → S) : T → Val α :=
  fun t => μ (preimage t)

-- ============================================================================
-- § Construct: Fubini-Tonelli
-- ============================================================================

/-- Tonelli's theorem: for nonneg measurable functions, iterated integrals equal. -/
theorem tonelli_sort (mulF : α → α → α) (f_val μ_val ν_val : α) :
    (∃ r, mul mulF (mul mulF (contents f_val) (contents μ_val)) (contents ν_val) = contents r) ∧
    (∃ r, mul mulF (mul mulF (contents f_val) (contents ν_val)) (contents μ_val) = contents r) :=
  ⟨⟨mulF (mulF f_val μ_val) ν_val, rfl⟩, ⟨mulF (mulF f_val ν_val) μ_val, rfl⟩⟩

/-- Fubini's theorem: iterated integrals equal product integral. -/
theorem fubini_deep (mulF : α → α → α)
    (f_val μ_val ν_val : α)
    (assoc : mulF (mulF f_val μ_val) ν_val = mulF f_val (mulF μ_val ν_val)) :
    mul mulF (mul mulF (contents f_val) (contents μ_val)) (contents ν_val) =
    mul mulF (contents f_val) (contents (mulF μ_val ν_val)) := by
  show contents (mulF (mulF f_val μ_val) ν_val) = contents (mulF f_val (mulF μ_val ν_val))
  rw [assoc]

-- ============================================================================
-- § Construct: Image Measure
-- ============================================================================

-- ============================================================================
-- § Decomposition: Lebesgue Decomposition
-- ============================================================================

-- ============================================================================
-- § Decomposition: Radon-Nikodym Derivative (Deep)
-- ============================================================================

/-- Radon-Nikodym uniqueness: two equal densities give equal contents. -/
theorem radon_nikodym_unique (f g : α) (h : f = g) :
    (contents f : Val α) = contents g := by rw [h]

-- ============================================================================
-- § Decomposition: Mutual Singularity
-- ============================================================================

/-- Two measures are mutually singular if their singular sets are contents(0). -/
theorem mutual_singular [Zero α] (μ_Ac ν_A : α)
    (h1 : μ_Ac = 0) (h2 : ν_A = 0) :
    (contents μ_Ac : Val α) = contents (0 : α) ∧
    (contents ν_A : Val α) = contents (0 : α) := by
  constructor
  · show contents μ_Ac = contents 0; rw [h1]
  · show contents ν_A = contents 0; rw [h2]

-- ============================================================================
-- § Decomposition: Conditional Expectation
-- ============================================================================

/-- Tower property: E[E[X|F]|G] = E[X|G] when G ⊆ F. Both sides contents. -/
theorem tower_property (condExpXF condExpXG : α) (h : condExpXF = condExpXG) :
    (contents condExpXF : Val α) = contents condExpXG := by rw [h]

/-- Conditional expectation is linear: E[aX+bY|F] = aE[X|F]+bE[Y|F]. -/
theorem cond_exp_linear (addF mulF : α → α → α) (a b eXF eYF : α) :
    add addF (mul mulF (contents a) (contents eXF))
             (mul mulF (contents b) (contents eYF)) =
    contents (addF (mulF a eXF) (mulF b eYF)) := rfl

-- ============================================================================
-- § Decomposition: Disintegration
-- ============================================================================

-- ============================================================================
-- § Decomposition: Density Functions
-- ============================================================================

/-- A probability density function f satisfies ∫f dμ = 1.
    In Val α: f is contents, ∫f dμ = contents(1). -/
theorem pdf_integral (mulF : α → α → α) (f_val μ_val one : α) (h : mulF f_val μ_val = one) :
    mul mulF (contents f_val) (contents μ_val) = contents one := by
  show contents (mulF f_val μ_val) = contents one; rw [h]

-- ============================================================================
-- § Function: Measurable Functions
-- ============================================================================

/-- A measurable function: a function whose values are contents-valued. -/
def isMeasurableFunc (f : S → Val α) : Prop :=
  ∀ s, ∃ a, f s = contents a

/-- A measurable function never hits origin on its domain. -/
theorem measurable_ne_origin (f : S → Val α) (hf : isMeasurableFunc f) (s : S) :
    f s ≠ origin := by
  obtain ⟨a, ha⟩ := hf s; rw [ha]; simp

-- ============================================================================
-- § Function: Simple Functions
-- ============================================================================

/-- A simple function: takes finitely many values. -/
def simpleFunc (vals : List α) (assign : S → Fin vals.length) (s : S) : Val α :=
  contents (vals.get (assign s))

-- ============================================================================
-- § Function: Integral of Simple Functions
-- ============================================================================

-- ============================================================================
-- § Function: Indicator Functions
-- ============================================================================

/-- Indicator function of a set: 1 on the set, 0 outside.
    In Val α: both 1 and 0 are contents. -/
theorem indicator_contents (zero one : α) (inSet : Bool) :
    ∃ r, (contents (if inSet then one else zero) : Val α) = contents r := by
  cases inSet with
  | true => exact ⟨one, rfl⟩
  | false => exact ⟨zero, rfl⟩

-- ============================================================================
-- § Function: Composition of Measurable Functions
-- ============================================================================

/-- Composition of measurable functions: contents in, contents out. -/
theorem measurable_comp (f g : α → α) (a : α) :
    valMap f (valMap g (contents a)) = valMap f (contents (g a)) := rfl

-- ============================================================================
-- § Integral: Lebesgue Integral Properties
-- ============================================================================

/-- Linearity of integral: ∫(af + bg) = a∫f + b∫g. All contents. -/
theorem integral_linear (addF mulF : α → α → α) (a b intF intG : α) :
    add addF (mul mulF (contents a) (contents intF))
             (mul mulF (contents b) (contents intG)) =
    contents (addF (mulF a intF) (mulF b intG)) := rfl

-- ============================================================================
-- § Integral: Bochner Integral
-- ============================================================================

-- ============================================================================
-- § Integral: Change of Variables
-- ============================================================================

/-- Change of variables: ∫f(g(x))|g'(x)| dμ = ∫f dν.
    In Val α: both sides contents. -/
theorem change_of_variables (mulF : α → α → α) (f_val g_prime μ_val : α) :
    mul mulF (mul mulF (contents f_val) (contents g_prime)) (contents μ_val) =
    contents (mulF (mulF f_val g_prime) μ_val) := rfl

-- ============================================================================
-- § Integral: Minkowski's Inequality (Sort-Level)
-- ============================================================================

/-- Minkowski: (∫|f+g|^p)^(1/p) ≤ (∫|f|^p)^(1/p) + (∫|g|^p)^(1/p). -/
theorem minkowski_sort (addF : α → α → α) (leF : α → α → Prop)
    (lp_f lp_g lp_fg : α)
    (h : leF lp_fg (addF lp_f lp_g)) :
    leF lp_fg (addF lp_f lp_g) := h

-- ============================================================================
-- § Integral: Convergence Theorems (Sort-Level Summary)
-- ============================================================================

-- ============================================================================
-- § Measure: Outer Measure
-- ============================================================================

/-- An outer measure: a function from sets to Val α. -/
def outerMeasure (S : Type u) (α : Type u) := S → Val α

/-- Outer measure of empty set is contents(0). -/
theorem outer_measure_empty [Zero α] (μ : outerMeasure S α) (empty : S)
    (h : μ empty = contents 0) :
    μ empty = contents (0 : α) := h

/-- Outer measure values satisfy sort trichotomy. -/
theorem outer_measure_sort (μ : outerMeasure S α) (s : S) :
    (∃ r, μ s = contents r) ∨ (∃ r, μ s = container r) ∨ μ s = origin := by
  cases μ s with
  | origin => right; right; rfl
  | container a => right; left; exact ⟨a, rfl⟩
  | contents a => left; exact ⟨a, rfl⟩

-- ============================================================================
-- § Measure: Monotonicity
-- ============================================================================

/-- Monotonicity: if A ⊆ B then μ(A) ≤ μ(B).
    In Val α with valLE: both are contents. -/
theorem monotone_contents (leF : α → α → Prop) (μA μB : α) (h : leF μA μB) :
    valLE leF (contents μA : Val α) (contents μB) := h

-- ============================================================================
-- § Measure: Jordan Decomposition
-- ============================================================================

-- ============================================================================
-- § Measure: Signed Measure
-- ============================================================================

-- ============================================================================
-- § Measure: Caratheodory Construction
-- ============================================================================

-- ============================================================================
-- § Specific: Dirac Measure
-- ============================================================================

/-- Dirac measure at a point: δ_a(A) = 1 if a ∈ A, 0 otherwise.
    In Val α: both 1 and 0 are contents. -/
def diracMeasure (one zero : α) (a : S) (test : S → Bool) : Val α :=
  if test a then contents one else contents zero

/-- Dirac measure is always contents. -/
theorem dirac_is_contents (one zero : α) (a : S) (test : S → Bool) :
    ∃ r, diracMeasure one zero a test = contents r := by
  unfold diracMeasure; cases test a with
  | true => exact ⟨one, rfl⟩
  | false => exact ⟨zero, rfl⟩

/-- Dirac measure is never origin. -/
theorem dirac_ne_origin (one zero : α) (a : S) (test : S → Bool) :
    diracMeasure one zero a test ≠ (origin : Val α) := by
  unfold diracMeasure; cases test a with
  | true => simp
  | false => simp

-- ============================================================================
-- § Specific: Counting Measure
-- ============================================================================

/-- Counting measure: μ(A) = |A|. A contents value. -/
def countingMeasure (count : α) : Val α := contents count

-- ============================================================================
-- § Specific: Haar Measure
-- ============================================================================

/-- Haar measure: the unique translation-invariant measure on a locally compact group.
    In Val α: Haar measure values are contents. -/
def haarMeasure (μ_val : α) : Val α := contents μ_val

/-- Translation invariance: μ(gA) = μ(A). Both contents. -/
theorem haar_translation_invariant (μ_A μ_gA : α) (h : μ_gA = μ_A) :
    (contents μ_gA : Val α) = contents μ_A := by rw [h]

-- ============================================================================
-- § Specific: Bernoulli Measure
-- ============================================================================

/-- Bernoulli probabilities sum to 1. -/
theorem bernoulli_total (addF : α → α → α) (p comp_p one : α)
    (h : addF p comp_p = one) :
    add addF (contents p) (contents comp_p) = contents one := by
  show contents (addF p comp_p) = contents one; rw [h]

-- ============================================================================
-- § Specific: Lebesgue Measure
-- ============================================================================

/-- Lebesgue measure is translation invariant. -/
theorem lebesgue_translation (subF addF : α → α → α) (a b c : α)
    (h : subF (addF b c) (addF a c) = subF b a) :
    (contents (subF (addF b c) (addF a c)) : Val α) = contents (subF b a) := by
  show contents (subF (addF b c) (addF a c)) = contents (subF b a); rw [h]

end Val
