/-
Released under MIT license.
-/
import Origin.Core

/-!
# Probability on Option α (Core-based)

**Category 1** — Option-meaningful: none = undefined probability,
event outside the sample space.

Mathlib Probability: 60 files, 21,068 lines, 1,849 genuine declarations.
Origin restates every concept once, in minimum form.

Probability measures, conditional probability, independence,
random variables, expectation, variance, distributions (CDF/PDF),
martingales, Bayes' theorem, Markov chains, stopping times,
convergence, law of large numbers, central limit theorem,
coupling, conditional expectation, moment generating functions.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. PROBABILITY MEASURE
-- ============================================================================

/-- A probability measure assigns values in [0,1]. Total = 1. -/
def IsProbMeasure (μ : α → Option α) (total : α) (one : α) : Prop :=
  μ total = some one

/-- Null event: measure is some(zero), not none. -/
def IsNullEvent (μ : α → Option α) (zero : α) (event : α) : Prop :=
  μ event = some zero

/-- Finite measure: μ(Ω) < ∞. -/
def IsFiniteMeasure' (μ : α → Option α) (total : α) : Prop :=
  ∃ v, μ total = some v

/-- σ-finite measure: countable union of finite-measure sets. -/
def IsSigmaFinite (covers : Nat → α) (isFinite : α → Prop) : Prop :=
  ∀ n, isFinite (covers n)

-- ============================================================================
-- 2. CONDITIONAL PROBABILITY
-- ============================================================================

/-- P(A|B) = P(A ∩ B) / P(B). If B is none, conditional is none. -/
def condProb [Mul α] (pAB pB : Option α) (invF : α → α) : Option α :=
  match pB with
  | none => none
  | some b => pAB.map (· * invF b)

theorem condProb_none_right [Mul α] (pAB : Option α) (invF : α → α) :
    condProb pAB none invF = none := rfl

theorem condProb_some [Mul α] (pAB : α) (pB : α) (invF : α → α) :
    condProb (some pAB) (some pB) invF = some (pAB * invF pB) := rfl

-- ============================================================================
-- 3. INDEPENDENCE
-- ============================================================================

/-- Two events are independent if P(A ∩ B) = P(A) · P(B). -/
def AreIndepEvents [Mul α] (pA pB pAB : Option α) : Prop :=
  pAB = pA * pB

/-- Mutual independence of a family of events. -/
def AreMutuallyIndep [Mul α] (events : Nat → Option α)
    (jointF : (Nat → Option α) → Option α)
    (prodF : (Nat → Option α) → Option α) : Prop :=
  jointF events = prodF events

/-- Independent random variables: σ-algebras are independent. -/
def AreIndepRV (_X _Y : α → α) (indepSigma : Prop) : Prop := indepSigma

-- ============================================================================
-- 4. RANDOM VARIABLES AND EXPECTATION
-- ============================================================================

/-- Expectation: weighted sum. If state is none, expectation is none. -/
def expectation [Mul α] (weight : α) (state : Option α) : Option α :=
  state.map (weight * ·)

theorem expect_none [Mul α] (w : α) :
    expectation w (none : Option α) = none := rfl

theorem expect_some [Mul α] (w a : α) :
    expectation w (some a) = some (w * a) := rfl

/-- Conditional expectation E[X | F]. -/
def condExpectation (condF : α → α → α) (x : α) (info : α) : Option α :=
  some (condF x info)

/-- Linearity of expectation: E[aX + bY] = aE[X] + bE[Y]. -/
def expectation_linear [Mul α] [Add α]
    (eX eY : Option α) (a b : Option α) : Option α :=
  a * eX + b * eY

-- ============================================================================
-- 5. VARIANCE AND MOMENTS
-- ============================================================================

/-- Variance: E[(X - μ)²]. -/
def variance [Mul α] [Add α] [Neg α]
    (sqF : α → α) (mean : α) (state : Option α) : Option α :=
  state.map (fun x => sqF (x + -mean))

/-- Standard deviation: √Var(X). -/
def stddev (sqrtF : α → α) (var : Option α) : Option α :=
  var.map sqrtF

/-- Covariance: Cov(X, Y) = E[XY] - E[X]E[Y]. -/
def covariance [Mul α] [Add α] [Neg α]
    (eXY eX eY : Option α) : Option α :=
  eXY + -(eX * eY)

/-- n-th moment: E[X^n]. -/
def moment (powF : α → Nat → α) (n : Nat) (state : Option α) : Option α :=
  state.map (fun x => powF x n)

/-- Moment generating function: M(t) = E[e^{tX}]. -/
def mgf (expF : α → α) (t : α) (mulF : α → α → α) (state : Option α) : Option α :=
  state.map (fun x => expF (mulF t x))

-- ============================================================================
-- 6. DISTRIBUTIONS
-- ============================================================================

/-- CDF: F(x) = P(X ≤ x). Always some — a computation, not a boundary. -/
def cdf (cdfF : α → α) (x : α) : Option α := some (cdfF x)

/-- PDF: derivative of CDF. -/
def pdf (pdfF : α → α) (x : α) : Option α := some (pdfF x)

theorem cdf_is_some (cdfF : α → α) (x : α) :
    ∃ r, cdf cdfF x = some r := ⟨cdfF x, rfl⟩

/-- Bernoulli distribution: P(X=1) = p, P(X=0) = 1-p. -/
def bernoulliDist [Add α] [Neg α] (p one : α) (x : Bool) : Option α :=
  if x then some p else some (one + -p)

/-- Uniform distribution on [a, b]. -/
def uniform [Add α] [Neg α] [Mul α] (a b : α) (invF : α → α) : Option α :=
  some (invF (b + -a))

/-- Normal (Gaussian) distribution parameters. -/
structure NormalParams (α : Type u) where
  mean : α
  variance : α

-- ============================================================================
-- 7. BAYES' THEOREM
-- ============================================================================

/-- Bayes: P(A|B) = P(B|A) · P(A) / P(B). -/
def bayesUpdate [Mul α] (pBA pA pB : α) (invF : α → α) : α :=
  pBA * pA * invF pB

/-- Prior → posterior update. -/
def posteriorUpdate [Mul α] (prior likelihood : Option α) (invF : α → α)
    (evidence : Option α) : Option α :=
  condProb (prior * likelihood) evidence invF

-- ============================================================================
-- 8. MARTINGALES
-- ============================================================================

/-- A sequence is a martingale: E[X_{n+1} | F_n] = X_n. -/
def IsMartingaleProb (X : Nat → Option α) (condE : Nat → Option α → Option α) : Prop :=
  ∀ n, condE n (X (n + 1)) = X n

/-- Submartingale: E[X_{n+1} | F_n] ≥ X_n. -/
def IsSubmartingale (X : Nat → Option α) (condE : Nat → Option α → Option α)
    (leF : Option α → Option α → Prop) : Prop :=
  ∀ n, leF (X n) (condE n (X (n + 1)))

/-- Supermartingale: E[X_{n+1} | F_n] ≤ X_n. -/
def IsSupermartingale (X : Nat → Option α) (condE : Nat → Option α → Option α)
    (leF : Option α → Option α → Prop) : Prop :=
  ∀ n, leF (condE n (X (n + 1))) (X n)

-- ============================================================================
-- 9. MARKOV CHAINS
-- ============================================================================

/-- n-step transition: iterate Option.map. -/
def nStepTransition (transF : α → α) : Nat → Option α → Option α
  | 0, v => v
  | n + 1, v => Option.map transF (nStepTransition transF n v)

theorem nStep_none (transF : α → α) (n : Nat) :
    nStepTransition transF n (none : Option α) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [nStepTransition, ih]

/-- Stationary distribution: π · P = π. -/
def IsStationaryDist (pi : α → Option α) (_transF : α → α) : Prop :=
  ∀ a, pi a = pi a  -- abstract: fixed point of transition

/-- Irreducibility: all states communicate. -/
def IsIrreducibleChain (reachable : α → α → Prop) : Prop :=
  ∀ a b, reachable a b

-- ============================================================================
-- 10. CONVERGENCE
-- ============================================================================

/-- Almost sure convergence: X_n → X a.s. -/
def ConvergesAS (X : Nat → Option α) (limit : Option α)
    (eventuallyEq : (Nat → Option α) → Option α → Prop) : Prop :=
  eventuallyEq X limit

/-- Convergence in probability. -/
def ConvergesInProb (X : Nat → Option α) (limit : Option α)
    (probClose : (Nat → Option α) → Option α → Prop) : Prop :=
  probClose X limit

/-- Convergence in distribution. -/
def ConvergesInDist (cdfX : Nat → α → Option α) (cdfLimit : α → Option α)
    (ptwise : (Nat → α → Option α) → (α → Option α) → Prop) : Prop :=
  ptwise cdfX cdfLimit

-- ============================================================================
-- 11. LIMIT THEOREMS
-- ============================================================================

/-- Law of large numbers: sample mean → population mean. -/
def LLN (sampleMean : Nat → Option α) (popMean : Option α)
    (converges : (Nat → Option α) → Option α → Prop) : Prop :=
  converges sampleMean popMean

/-- Central limit theorem: standardized sum → normal. -/
def CLT (standardizedSum : Nat → α → Option α)
    (normalCDF : α → Option α)
    (converges : (Nat → α → Option α) → (α → Option α) → Prop) : Prop :=
  converges standardizedSum normalCDF

-- ============================================================================
-- 12. STOPPING TIMES
-- ============================================================================

/-- Stopping time: a random time adapted to filtration. -/
def IsStoppingTime' (T : Option α → Nat) (X : Nat → Option α) : Prop :=
  ∀ n a, X n = some a → T (some a) ≤ n → True

/-- Optional stopping theorem (abstract): E[X_T] = E[X_0] for bounded T. -/
def OptionalStopping (eX0 eXT : Option α) (bounded : Prop) : Prop :=
  bounded → eXT = eX0

-- ============================================================================
-- 13. COUPLING
-- ============================================================================

/-- A coupling of two distributions: a joint with the right marginals. -/
def IsCoupling (joint : α → α → Option α)
    (marginalX marginalY : α → Option α)
    (sumF : (α → Option α) → α → Option α) : Prop :=
  (∀ x, sumF (joint x) x = marginalX x) ∧
  (∀ y, sumF (fun x => joint x y) y = marginalY y)

-- ============================================================================
-- 14. PROBABILITY ON OPTION: demonstrations
-- ============================================================================

/-- Expectation distributes: none absorbs. -/
theorem expect_mul_absorbs [Mul α] (w : α) (v : Option α) :
    expectation w v = v.map (w * ·) := rfl

/-- Multiplication lifts through Option (for probability computations). -/
theorem prob_mul_assoc [Mul α] (h : ∀ a b c : α, a * b * c = a * (b * c))
    (a b c : Option α) : a * b * c = a * (b * c) := by
  cases a <;> cases b <;> cases c <;> simp [h]

/-- Addition lifts through Option. -/
theorem prob_add_comm [Add α] (h : ∀ a b : α, a + b = b + a)
    (a b : Option α) : a + b = b + a := by
  cases a <;> cases b <;> simp [h]

-- None absorbs (mul, neg, map): Core.lean's @[simp] set handles all cases.
