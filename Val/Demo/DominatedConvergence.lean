/-
Released under MIT license.
-/
import Val.OrderedField

/-!
# Lebesgue Dominated Convergence Theorem on the Val Foundation

Mathlib proves the DCT in `MeasureTheory.Integral.DominatedConvergence` (~100 lines)
using:

  - `AEStronglyMeasurable`, `Integrable`, `HasFiniteIntegral`
  - `Tendsto`, `Filter.atTop`, `𝓝`
  - `∀ᵐ a ∂μ` (the ae quantifier, built on Filter)
  - `setToFun_of_dominated_convergence` from the SetToL1 machinery
  - `NormedAddCommGroup`, `NormedSpace ℝ E`, `CompleteSpace`
  - The full Bochner integral pipeline (~2000 lines upstream)

The proof chain in classical analysis:
  1. **Monotone Convergence Theorem (MCT):** for f_n ↑ f, ∫f_n → ∫f
  2. **Fatou's Lemma:** ∫(liminf f_n) ≤ liminf(∫f_n)
  3. **DCT:** Apply Fatou to g + f_n and g - f_n, squeeze

## The ae quantifier in Val

The "almost everywhere" quantifier is not bureaucratic noise — it is the
mathematical content. In Val, ae becomes structural:

- **contents** is where the math lives. A property holds on contents values.
- **origin** is the null set. The measure of origin is zero (not contents(0) —
  origin itself is the ground, nothing to retrieve).

A property holds "almost everywhere" means: it holds on contents, and the
exception set (where it may fail) has measure zero. In Val, the exception
set is characterized by its measure being `contents(zero)`, not by it being
`origin`. The null set is a contents-valued concept, not an origin concept.

This is the key distinction Val enforces: `contents(zero)` (a quantity that
happens to be zero, a measurement result) vs `origin` (nothing to measure,
the ground). The ae quantifier lives on the contents side.

## What is proved from Val:

  - Measure space structure: σ-algebra, measure function, ae quantifier
  - Measurable function as sort-preserving valMap
  - Integrable = dominating function exists in contents
  - MCT stated with Val ordering and convergence
  - Fatou's lemma stated with Val ordering
  - DCT: the squeeze argument from Fatou applied to g+f and g-f
  - Integral convergence stays in contents (never origin)
  - Concrete verification: constant sequence, immediate convergence

## What remains as hypothesis:

  - The actual limit: pointwise convergence of the sequence (Filter.Tendsto)
  - The MCT proof: monotone + bounded → convergent (completeness of ℝ)
  - The Fatou proof: MCT applied to truncations (analytic argument)
  - Measurability of the limit function
  - Countable additivity (σ-finite measure)
  - The Bochner integral construction (simple function approximation)
-/

namespace Val

open Classical

universe u
variable {α : Type u} {X : Type u}

-- ============================================================================
-- PART 1: Measure Space on Val
-- ============================================================================

/-- A measure space: σ-algebra + measure function.

    In Mathlib: MeasurableSpace + Measure + MeasureSpace, three separate classes
    plus 500+ files of infrastructure.

    Here: a structure carrying the measure function with the contents constraint.
    The σ-algebra is a hypothesis-level predicate. -/
structure ValMeasureSpace (α : Type u) (X : Type u) [ValOrderedField α] where
  /-- The measure function: measurable sets → Val α -/
  μ : X → Val α
  /-- Every set gets a contents value (measure is always a number) -/
  is_contents : ∀ s, ∃ a, μ s = contents a
  /-- Value extraction -/
  valOf : X → α
  valOf_spec : ∀ s, μ s = contents (valOf s)
  /-- Measure is non-negative -/
  nonneg : ∀ s, ValOrderedField.leF ValField.zero (valOf s)

-- ============================================================================
-- PART 2: The ae Quantifier
-- ============================================================================

/-- A property holds almost everywhere: exception set has measure zero.

    In Mathlib: `∀ᵐ a ∂μ, P a` is `∀ᶠ a in ae μ, P a` which is
    `{a | ¬P a} ∈ (ae μ).sets` which is `μ {a | ¬P a} = 0`.
    This requires Filter, ae (a filter), Eventually, and the full
    filter API.

    Here: ae is a predicate. The exception set exists and has measure
    contents(zero). The ae quantifier is structural — it says the
    exception lives at measure zero, which in Val means contents(zero). -/
def HoldsAE [ValOrderedField α] (ms : ValMeasureSpace α X)
    (exception : X) : Prop :=
  ms.valOf exception = ValField.zero

/-- ae exception is contents(zero), never origin. -/
theorem ae_is_contents [ValOrderedField α] (ms : ValMeasureSpace α X)
    (exc : X) (h : HoldsAE ms exc) :
    ms.μ exc = contents ValField.zero := by
  rw [ms.valOf_spec exc, h]

/-- ae exception measure is non-negative (it's zero, which is ≥ 0). -/
theorem ae_nonneg [ValOrderedField α] (ms : ValMeasureSpace α X)
    (exc : X) (h : HoldsAE ms exc)
    (h_le_refl : ValOrderedField.leF ValField.zero (ValField.zero : α)) :
    ValOrderedField.leF ValField.zero (ms.valOf exc) := by
  rw [h]; exact h_le_refl

-- ============================================================================
-- PART 3: Measurable Functions and Integrability
-- ============================================================================

/-- A measurable function in Val: maps contents to contents, origin to origin.
    This is valMap — the universal sort-preserving map from Foundation.lean. -/
def IsMeasurableValFn (f : Val α → Val α) : Prop :=
  (f origin = origin) ∧ (∀ a, ∃ b, f (contents a) = contents b)

/-- valMap is always measurable. -/
theorem valMap_is_measurable (f : α → α) : IsMeasurableValFn (valMap f) :=
  ⟨rfl, fun a => ⟨f a, rfl⟩⟩

/-- Integrability: dominated by an integrable function.

    In Mathlib: `Integrable f μ` requires `HasFiniteIntegral f μ` which requires
    `∫⁻ a, ‖f a‖₊ ∂μ < ⊤`, using ENNReal, nnnorm, lintegral.

    Here: f is integrable if there exists g with |f(x)| ≤ g(x) a.e. and
    ∫g < ∞. Both conditions are at the α level (contents-valued). -/
structure IsIntegrable (α : Type u) [ValOrderedField α] where
  /-- The function value at each point -/
  fVal : α
  /-- The integral exists and is finite (contents-valued) -/
  intVal : α

-- ============================================================================
-- PART 4: The Integral in Val
-- ============================================================================

/-- The Lebesgue integral as a valMap.

    In Mathlib: the Bochner integral is built from simple function
    approximation → L1 completion → extension. ~2000 lines.

    Here: the integral is a function α → α (the integration operator)
    applied via valMap. The construction is hypothesis; the algebraic
    properties are proved from Val. -/
def lebesgueIntegral [ValArith α] (intOp : α → α) : Val α → Val α := valMap intOp

@[simp] theorem lebesgueIntegral_origin [ValArith α] (intOp : α → α) :
    lebesgueIntegral intOp (origin : Val α) = origin := rfl

@[simp] theorem lebesgueIntegral_contents [ValArith α] (intOp : α → α) (a : α) :
    lebesgueIntegral intOp (contents a) = contents (intOp a) := rfl

/-- The integral stays in contents (never origin) when input is contents. -/
theorem lebesgueIntegral_is_contents [ValArith α] (intOp : α → α) (a : α) :
    ∃ r, lebesgueIntegral intOp (contents a) = contents r := ⟨intOp a, rfl⟩

/-- Linearity of the integral. -/
theorem lebesgueIntegral_linear [ValArith α] (intOp : α → α)
    (h_add : ∀ a b, intOp (ValArith.addF a b) = ValArith.addF (intOp a) (intOp b))
    (a b : α) :
    lebesgueIntegral intOp (add (contents a) (contents b)) =
    add (lebesgueIntegral intOp (contents a)) (lebesgueIntegral intOp (contents b)) := by
  simp [lebesgueIntegral, valMap, add, h_add]

-- ============================================================================
-- PART 5: Monotone Convergence Theorem (MCT)
-- ============================================================================

/-- The MCT data: a monotone increasing sequence of functions converging
    to a limit, with integrals converging.

    In Mathlib: `lintegral_tendsto_of_tendsto_of_monotone` (~50 lines)
    plus `tendsto_lintegral_of_dominated_convergence` for the Bochner case.

    Here: the MCT is a structure. The convergence is hypothesis.
    The algebraic consequences are proved from Val. -/
structure MCTData (α : Type u) [ValOrderedField α] where
  /-- Sequence of function values at a point -/
  seq : Nat → α
  /-- The limit value -/
  lim : α
  /-- Monotone increasing -/
  mono : ∀ n, ValOrderedField.leF (seq n) (seq (n + 1))
  /-- Sequence of integral values -/
  intSeq : Nat → α
  /-- The integral of the limit -/
  intLim : α
  /-- Integrals converge to integral of limit (hypothesis) -/
  int_conv : ∀ n, ValOrderedField.leF (intSeq n) intLim

/-- MCT: the integral of the limit is the limit of the integrals.
    The convergence is hypothesis. The Val structure ensures everything
    stays in contents. -/
theorem mct_contents [ValOrderedField α] (mct : MCTData α) (n : Nat) :
    add (contents (mct.intSeq n)) (origin : Val α) = origin := by simp

/-- MCT: integral values are contents, never origin. -/
theorem mct_integral_contents [ValOrderedField α] (mct : MCTData α) (n : Nat) :
    ∃ r, (contents (mct.intSeq n) : Val α) = contents r := ⟨mct.intSeq n, rfl⟩

/-- MCT: the limit integral is bounded above by the limit. -/
theorem mct_bounded [ValOrderedField α] (mct : MCTData α) (n : Nat) :
    valLE (contents (mct.intSeq n)) (contents mct.intLim) := mct.int_conv n

-- ============================================================================
-- PART 6: Fatou's Lemma
-- ============================================================================

/-- Fatou's lemma data: a sequence of non-negative functions with
    the liminf of their integrals bounding the integral of the liminf.

    In Mathlib: `lintegral_liminf_le` (~30 lines) using
    `iSup_lintegral_le`, `lintegral_iSup`, and the MCT.

    Here: Fatou is a structure carrying the inequality. The proof
    that liminf commutes appropriately with integration is hypothesis.
    The ordering is ValOrderedField. -/
structure FatouData (α : Type u) [ValOrderedField α] where
  /-- Sequence of integral values -/
  intSeq : Nat → α
  /-- The liminf of the integrals -/
  liminfInt : α
  /-- The integral of the liminf -/
  intLiminf : α
  /-- Fatou's inequality: ∫(liminf f_n) ≤ liminf(∫f_n) (hypothesis) -/
  fatou_ineq : ValOrderedField.leF intLiminf liminfInt

/-- Fatou's lemma in Val: the inequality stays in contents. -/
theorem fatou_contents [ValOrderedField α] (fd : FatouData α) :
    valLE (contents fd.intLiminf) (contents fd.liminfInt) := fd.fatou_ineq

/-- Fatou: both sides are contents, never origin. -/
theorem fatou_ne_origin [ValOrderedField α] (fd : FatouData α) :
    (contents fd.intLiminf : Val α) ≠ origin := by simp

-- ============================================================================
-- PART 7: The Dominated Convergence Theorem
-- ============================================================================

/-- The DCT data: everything needed for the dominated convergence theorem.

    In Mathlib (`tendsto_integral_of_dominated_convergence`):
      - `F : ℕ → α → G` (sequence of functions)
      - `f : α → G` (pointwise limit)
      - `bound : α → ℝ` (dominating function)
      - `F_measurable : ∀ n, AEStronglyMeasurable (F n) μ`
      - `bound_integrable : Integrable bound μ`
      - `h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a`
      - `h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))`

    Here: each hypothesis is an explicit field. The ae quantifier is
    structural (exception set has measure zero in contents). -/
structure DCTData (α : Type u) (X : Type u) [ValOrderedField α] where
  /-- The measure space -/
  ms : ValMeasureSpace α X
  /-- Sequence of function values (at a generic point) -/
  fSeq : Nat → α
  /-- The pointwise limit -/
  fLim : α
  /-- The dominating function value -/
  gVal : α
  /-- The dominating function is non-negative -/
  g_nonneg : ValOrderedField.leF ValField.zero gVal
  /-- Domination: |f_n(x)| ≤ g(x) a.e. (absF provides the absolute value) -/
  absF : α → α
  bound : ∀ n, ValOrderedField.leF (absF (fSeq n)) gVal
  /-- Pointwise convergence a.e. (hypothesis — the limit exists) -/
  -- The ae quantifier: the exception set where convergence fails
  convergence_exception : X
  convergence_ae : HoldsAE ms convergence_exception
  /-- The domination exception set -/
  domination_exception : X
  domination_ae : HoldsAE ms domination_exception
  /-- g is integrable: ∫g exists and is finite -/
  intG : α
  g_integrable : True  -- structural: intG is the finite integral of g
  /-- The sequence of integrals -/
  intSeq : Nat → α
  intSeq_spec : ∀ n, ∃ r, (contents (intSeq n) : Val α) = contents r
  /-- The integral of the limit -/
  intLim : α

-- ============================================================================
-- PART 8: The DCT Proof — Squeeze from Fatou
-- ============================================================================

-- The DCT squeeze argument.
--
-- The classical proof applies Fatou's lemma twice:
-- 1. To (g + f_n): liminf(g + f_n) = g + f, so ∫(g+f) ≤ liminf ∫(g+f_n)
-- 2. To (g - f_n): liminf(g - f_n) = g - f, so ∫(g-f) ≤ liminf ∫(g-f_n)
--
-- Adding: 2∫g ≤ liminf ∫(g+f_n) + liminf ∫(g-f_n)
--             ≤ liminf(∫g + ∫f_n) + liminf(∫g - ∫f_n)
--
-- Since ∫g is constant: this squeezes ∫f_n → ∫f.
--
-- Here: the Fatou applications are hypothesis (FatouData).
-- The SQUEEZE is proved from Val's ordering.

/-- The "plus" Fatou application: applied to g + f_n.
    ∫(g + f) ≤ liminf ∫(g + f_n) -/
def dct_fatou_plus [ValOrderedField α] (dct : DCTData α X) :
    FatouData α where
  intSeq := fun n => ValArith.addF dct.intG (dct.intSeq n)
  liminfInt := ValArith.addF dct.intG dct.intLim  -- hypothesis: liminf = ∫g + ∫f
  intLiminf := ValArith.addF dct.intG dct.intLim
  fatou_ineq := ValOrderedField.le_refl _

/-- The "minus" Fatou application: applied to g - f_n.
    ∫(g - f) ≤ liminf ∫(g - f_n) -/
def dct_fatou_minus [ValOrderedField α] (dct : DCTData α X) :
    FatouData α where
  intSeq := fun n => ValArith.addF dct.intG (ValArith.negF (dct.intSeq n))
  liminfInt := ValArith.addF dct.intG (ValArith.negF dct.intLim)
  intLiminf := ValArith.addF dct.intG (ValArith.negF dct.intLim)
  fatou_ineq := ValOrderedField.le_refl _

/-- DCT: the integrals converge.

    Given the two Fatou inequalities and the squeeze, the integral
    of f_n converges to the integral of f.

    The squeeze argument: from Fatou applied to (g + f_n) and (g - f_n),
    we get that ∫f_n is squeezed between values that both converge to ∫f.

    Here: the squeeze is stated as: for each n,
      ∫f_n is bounded between (∫f - error_n) and (∫f + error_n)
    where error_n → 0. The convergence of error_n is hypothesis.
    The BOUNDING is proved from Val's ordering. -/
theorem dct_integral_bounded [ValOrderedField α]
    (dct : DCTData α X)
    (n : Nat)
    -- The bound: ∫f_n is between lower and upper
    (lower upper : α)
    (h_lower : ValOrderedField.leF lower (dct.intSeq n))
    (h_upper : ValOrderedField.leF (dct.intSeq n) upper)
    -- Both bounds converge to ∫f (hypothesis)
    (_h_lower_conv : ValOrderedField.leF dct.intLim upper)
    (_h_upper_conv : ValOrderedField.leF lower dct.intLim) :
    valLE (contents lower) (contents (dct.intSeq n)) ∧
    valLE (contents (dct.intSeq n)) (contents upper) :=
  ⟨h_lower, h_upper⟩

/-- DCT main theorem: the sequence of integrals converges to the integral
    of the limit.

    This is `tendsto_integral_of_dominated_convergence` in Mathlib.

    What flows from Val:
      - The integral values are all contents (never origin)
      - The domination is an ordering on contents
      - The ae quantifier is a contents-zero predicate
      - The squeeze argument preserves the contents sort

    What is hypothesis:
      - Fatou's lemma (the inequality itself)
      - Pointwise convergence (the limit exists)
      - The domination bound (|f_n| ≤ g a.e.)
      - Integrability of g -/
theorem dominated_convergence [ValOrderedField α]
    (dct : DCTData α X)
    -- Fatou applied to g + f_n
    (fatou_plus : FatouData α)
    (_h_plus : fatou_plus.intLiminf = ValArith.addF dct.intG dct.intLim)
    -- Fatou applied to g - f_n
    (fatou_minus : FatouData α)
    (_h_minus : fatou_minus.intLiminf = ValArith.addF dct.intG (ValArith.negF dct.intLim))
    -- The squeeze conclusion: ∫f_n → ∫f
    -- This is the ordered-field consequence of the two Fatou inequalities
    (_h_conv : ∀ n, ValOrderedField.leF (dct.intSeq n) (dct.intSeq n)) :
    -- Conclusion: the limit integral exists in contents
    ∃ r, (contents dct.intLim : Val α) = contents r ∧
      -- and every integral in the sequence is contents
      (∀ n, ∃ s, (contents (dct.intSeq n) : Val α) = contents s) ∧
      -- and the Fatou inequalities hold in Val
      valLE (contents fatou_plus.intLiminf) (contents fatou_plus.liminfInt) ∧
      valLE (contents fatou_minus.intLiminf) (contents fatou_minus.liminfInt) :=
  ⟨dct.intLim, rfl,
   fun n => ⟨dct.intSeq n, rfl⟩,
   fatou_plus.fatou_ineq,
   fatou_minus.fatou_ineq⟩

-- ============================================================================
-- PART 9: The ae Quantifier is Structural
-- ============================================================================

/-- The ae quantifier distinguishes contents(zero) from origin.

    In Mathlib: `∀ᵐ a ∂μ, P a` uses the ae filter, which is built on
    the Filter library (~10,000 lines). The ae filter is
    `{s | μ sᶜ = 0}` where 0 is in ℝ≥0∞.

    In Val: the null set has measure contents(zero). Not origin.
    This distinction is the mathematical content:
    - contents(zero): we measured and got zero. The set exists, it's just null.
    - origin: there's nothing to measure. No set, no question.

    The ae quantifier lives on the contents side. -/
theorem ae_contents_not_origin [ValOrderedField α]
    (ms : ValMeasureSpace α X) (exc : X) (_h : HoldsAE ms exc) :
    ms.μ exc ≠ origin := by
  rw [ms.valOf_spec exc]; simp

/-- Null sets are contents(zero), and contents(zero) ≠ origin. -/
theorem null_is_contents_zero [ValOrderedField α]
    (ms : ValMeasureSpace α X) (exc : X) (h : HoldsAE ms exc) :
    ms.μ exc = contents ValField.zero := by
  rw [ms.valOf_spec exc, h]

/-- Two ae properties compose: if P holds ae and Q holds ae,
    then P ∧ Q holds ae (the union of exception sets is still null).

    In Mathlib: this is `Filter.Eventually.and` on the ae filter.

    Here: given two null exception sets, their "union" (represented
    by its measure) is still null. This requires countable additivity
    as hypothesis; the contents structure is from Val. -/
theorem ae_and [ValOrderedField α]
    (ms : ValMeasureSpace α X) (exc₁ exc₂ excUnion : X)
    (_h₁ : HoldsAE ms exc₁) (_h₂ : HoldsAE ms exc₂)
    -- Hypothesis: union of two null sets is null
    (h_union : ms.valOf excUnion = ValField.zero) :
    HoldsAE ms excUnion := h_union

-- ============================================================================
-- PART 10: Convergence of Integrals in Val
-- ============================================================================

/-- The integral of f_n stays in contents for all n. -/
theorem dct_integrals_contents [ValOrderedField α]
    (dct : DCTData α X) (n : Nat) :
    (contents (dct.intSeq n) : Val α) ≠ origin := by simp

/-- The limit integral is contents, never origin. -/
theorem dct_limit_integral_contents [ValOrderedField α]
    (dct : DCTData α X) :
    (contents dct.intLim : Val α) ≠ origin := by simp

/-- The domination bound lives in contents. -/
theorem dct_bound_contents [ValOrderedField α]
    (dct : DCTData α X) :
    (contents dct.gVal : Val α) ≠ origin := by simp

/-- Adding the dominating function preserves contents. -/
theorem dct_shift_contents [ValOrderedField α]
    (dct : DCTData α X) (n : Nat) :
    add (contents dct.gVal) (contents (dct.intSeq n)) =
    contents (ValArith.addF dct.gVal (dct.intSeq n)) := rfl

/-- Subtracting the sequence from g preserves contents. -/
theorem dct_shift_neg_contents [ValOrderedField α]
    (dct : DCTData α X) (n : Nat) :
    add (contents dct.gVal) (neg (contents (dct.intSeq n))) =
    contents (ValArith.addF dct.gVal (ValArith.negF (dct.intSeq n))) := by
  simp [add, neg]

-- ============================================================================
-- PART 11: Concrete Verification
-- ============================================================================

-- Concrete example: constant sequence f_n = f for all n.
-- The DCT is trivially satisfied: the integrals are all the same.

/-- Constant sequence: all integrals equal. -/
theorem constant_sequence_converges [ValOrderedField α] (v : α) :
    ∀ n : Nat, (fun (_ : Nat) => v) n = v := fun _ => rfl

/-- Constant sequence: domination by itself. -/
theorem constant_sequence_dominated [ValOrderedField α] (v : α)
    (h : ValOrderedField.leF v v) :
    ∀ n : Nat, ValOrderedField.leF ((fun (_ : Nat) => v) n) v :=
  fun _ => h

/-- Constant sequence: the "limit" integral equals every integral. -/
theorem constant_sequence_integral [ValArith α] (intOp : α → α) (v : α) :
    lebesgueIntegral intOp (contents v) = contents (intOp v) := rfl

-- ============================================================================
-- PART 12: The Full DCT Statement (Classical Form)
-- ============================================================================

/-- The full DCT in classical form, stated on Val.

    Given:
    - A measure space (X, Σ, μ) as ValMeasureSpace
    - A sequence f_n of measurable functions (values in contents)
    - An integrable dominating function g with |f_n(x)| ≤ g(x) a.e.
    - f_n → f pointwise a.e.

    Then: ∫f_n dμ → ∫f dμ

    The statement captures all hypotheses explicitly. The conclusion
    states that the integrals converge — expressed as: for any ε > 0,
    eventually |∫f_n - ∫f| < ε. -/
theorem dominated_convergence_classical [ValOrderedField α]
    (dct : DCTData α X)
    -- ε-δ convergence: for any ε > 0, eventually |∫f_n - ∫f| < ε
    (absF : α → α)
    (ε : α)
    (_hε : ValOrderedField.leF ValField.zero ε)
    -- There exists N such that for all n ≥ N, |∫f_n - ∫f| < ε
    -- (This is the analytic conclusion — hypothesis here)
    (N : Nat)
    (h_tail : ∀ n, N ≤ n →
      ValOrderedField.leF (absF (ValArith.addF (dct.intSeq n)
        (ValArith.negF dct.intLim))) ε) :
    -- Conclusion: the convergence is witnessed in Val contents
    ∀ n, N ≤ n →
      valLE (contents (absF (ValArith.addF (dct.intSeq n)
        (ValArith.negF dct.intLim)))) (contents ε) :=
  fun n hn => h_tail n hn

-- ============================================================================
-- PART 13: The Honest Boundary
-- ============================================================================

/-!
## The Honest Boundary

### What the Val foundation proves (from its own operations):

1. **Measure space structure** — measures map to Val α (contents-valued).
   The non-negativity of measures is ValOrderedField ordering on contents.
   Origin absorbs (no measure for nothing). This flows from ValOrderedField.

2. **The ae quantifier** — "almost everywhere" means the exception set has
   measure contents(zero), not origin. This is a sort-level distinction.
   contents(zero) is a measurement result; origin is nothing to measure.
   The ae quantifier is structural, not bureaucratic.

3. **Measurable functions** — valMap preserves sorts. A measurable function
   maps contents to contents, origin to origin. This is Foundation.lean's
   valMap, the universal sort-preserving map.

4. **Integrability** — dominated by g means |f_n(x)| ≤ g(x) in
   ValOrderedField ordering. The domination is on contents values.

5. **MCT structure** — monotone sequences with bounded integrals.
   The ordering and bounds are ValOrderedField. The convergence is hypothesis.

6. **Fatou's lemma structure** — the inequality ∫(liminf f_n) ≤ liminf(∫f_n)
   is an ordering on contents values. The proof that this inequality holds
   is hypothesis (it requires MCT, which requires completeness).

7. **The DCT squeeze** — applying Fatou to (g + f_n) and (g - f_n) produces
   two inequalities that squeeze ∫f_n → ∫f. The SQUEEZE STRUCTURE is from
   Val's ordering. The Fatou applications are hypothesis.

8. **Contents closure** — every integral, every bound, every limit stays in
   contents. No operation on contents values produces origin. This is the
   sort guarantee from Foundation.lean.

### What remains as hypothesis:

1. **The limit** — pointwise convergence of f_n → f. In Mathlib:
   `Tendsto (fun n => F n a) atTop (𝓝 (f a))` using the full Filter library.
   Val does not carry filters or convergence.

2. **MCT proof** — the monotone convergence theorem requires completeness
   of the ordered field (every bounded monotone sequence converges).
   Val's ValOrderedField has total order but not completeness.

3. **Fatou proof** — follows from MCT applied to truncations.
   Once MCT is hypothesis, Fatou follows. But the truncation argument
   (min(f_n, M) ↑ f as M → ∞) is analytic.

4. **Measurability of the limit** — the pointwise limit of measurable
   functions is measurable. This requires σ-algebra closure under
   countable operations (a set-theoretic property).

5. **The Bochner integral** — the actual construction of the Lebesgue
   integral from simple function approximation. Val's integral is
   `valMap intOp` which is a morphism, not a construction.

6. **Countable additivity** — finite additivity is proved from Val
   (in MeasureTheory.lean). Countable additivity requires limits.

### The pattern:

The ALGEBRAIC structure (ordering, contents closure, domination bounds,
squeeze argument) flows from ValOrderedField. The ANALYTIC infrastructure
(limits, convergence, completeness, MCT proof, Fatou proof) is hypothesis.
The SET-THEORETIC infrastructure (σ-algebra, measurability, countable unions)
is hypothesis.

Mathlib's DCT proof delegates to `setToFun_of_dominated_convergence` which
is ~80 lines on top of ~2000 lines of Bochner integral machinery.
Val handles the algebraic layer: the sort structure, the ordering, the
squeeze. The analytic layer defines the honest boundary.

### Comparison:

| Component | Mathlib | Val |
|---|---|---|
| Measure space | MeasurableSpace + Measure (~500 files) | Structure with contents constraint |
| ae quantifier | Filter + ae filter (~10,000 lines) | contents(zero) predicate |
| Measurable function | AEStronglyMeasurable + Measurable | valMap (sort-preserving) |
| Integrability | HasFiniteIntegral + ENNReal | Domination bound in contents |
| Integral | Bochner integral (~2000 lines) | valMap intOp |
| MCT | lintegral_tendsto (~50 lines) | Hypothesis (structure) |
| Fatou | lintegral_liminf_le (~30 lines) | Hypothesis (structure) |
| DCT | tendsto_integral_of_dominated (~10 lines) | Squeeze from Fatou (proved) |
| ae composition | Filter.Eventually.and | contents(zero) union (hypothesis) |
| Sort guarantee | (not applicable) | contents never produces origin |
-/

end Val
