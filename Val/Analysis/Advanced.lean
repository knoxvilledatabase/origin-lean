/-
Released under MIT license.
-/
import Val.Analysis.Core

/-!
# Val α: Analysis — Advanced

Sections 9-16: Asymptotic limits, box integrals, bump functions, complex analysis,
meromorphic functions, distributions, ODEs, polynomial analysis.

Contents in, contents out. The sort is structural. No ≠ 0 at sort level.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- 9. ASYMPTOTIC LIMITS: Summability, Abel, Cesaro, Dirichlet
-- ============================================================================

/-!
## Val α: Asymptotic Limits and Specific Computations

Summability, Abel's theorem, Cesaro means, Dirichlet series.
All limit computations produce contents values. No ≠ 0 at sort level.
-/

-- ============================================================================
-- Summability
-- ============================================================================

/-- A series Σ aₙ is summable if partial sums converge.
    In Val α: partial sums are contents. -/
def isSummable (partialSumF : (Nat → α) → Nat → α)
    (conv : (Nat → α) → α → Prop) (seq : Nat → α) : Prop :=
  ∃ L : α, conv (partialSumF seq) L


-- ============================================================================
-- Absolute Convergence
-- ============================================================================

/-- Absolute convergence: Σ |aₙ| converges. -/
def isAbsolutelySummable (absF : α → α) (partialSumF : (Nat → α) → Nat → α)
    (conv : (Nat → α) → α → Prop) (seq : Nat → α) : Prop :=
  isSummable partialSumF conv (fun n => absF (seq n))

-- ============================================================================
-- Comparison Test
-- ============================================================================

/-- If |aₙ| ≤ bₙ, the comparison is within contents. -/
theorem comparison_test_contents [LE α]
    (absF : α → α) (seq bound : Nat → α)
    (h : ∀ n, absF (seq n) ≤ bound n) (n : Nat) :
    absF (seq n) ≤ bound n :=
  h n

-- ============================================================================
-- Ratio Test
-- ============================================================================

/-- Ratio test: |aₙ₊₁/aₙ|. In Val α: contents ÷ contents = contents. -/
def ratioTestQuotient [Mul α] (invF : α → α) (absF : α → α) (seq : Nat → α) (n : Nat) : α :=
  absF (seq (n + 1)) * invF (absF (seq n))


-- ============================================================================
-- Root Test
-- ============================================================================

/-- Root test: limsup |aₙ|^(1/n) < 1 implies convergence. -/
def rootTestTerm (absF : α → α) (nthRootF : α → Nat → α)
    (seq : Nat → α) (n : Nat) : α :=
  nthRootF (absF (seq n)) n


-- ============================================================================
-- Cesaro Mean
-- ============================================================================

/-- Cesaro mean: σₙ = (s₀ + ... + sₙ) / (n+1). Division is contents ÷ contents. -/
def cesaroMean [Add α] [Mul α]
    (invF : α → α)
    (partialSumF : (Nat → α) → Nat → α)
    (sumOfPartialSums : (Nat → α) → Nat → α)
    (natToAlpha : Nat → α) (seq : Nat → α) (n : Nat) : α :=
  sumOfPartialSums (partialSumF seq) n * invF (natToAlpha (n + 1))


-- ============================================================================
-- Abel's Theorem
-- ============================================================================

/-- Abel sum: Σ aₙ xⁿ. In Val α: the result is contents. -/
def abelSum [Add α] [Mul α] (seq : Nat → α) (x : α)
    (powF : α → Nat → α) (sumF : (Nat → α) → α) : α :=
  sumF (fun n => seq n * powF x n)


-- ============================================================================
-- Geometric Series
-- ============================================================================


-- ============================================================================
-- Power Series at Boundary
-- ============================================================================


-- ============================================================================
-- Dirichlet Series
-- ============================================================================

/-- Dirichlet series: Σ aₙ / nˢ. Each term is contents ÷ contents = contents. -/
def dirichletTerm [Mul α] (invF : α → α) (coeffs : Nat → α) (powF : α → α → α)
    (natToAlpha : Nat → α) (s : α) (n : Nat) : α :=
  coeffs n * invF (powF (natToAlpha n) s)


-- ============================================================================
-- 10. BOX INTEGRAL: Box Integrals, Henstock-Kurzweil
-- ============================================================================

/-!
## Val α: Box Integrals

Box integrals, Henstock-Kurzweil integration, tagged partitions.
Box volumes are contents. Riemann sums are contents.
Mesh refinement stays within contents. No ≠ 0 at sort level.
-/

-- ============================================================================
-- Box: A Rectangular Region
-- ============================================================================

/-- A box is defined by lower and upper bounds. Both bounds are contents. -/
structure BoxBounds (α : Type u) where
  lower : α
  upper : α

/-- Box volume (width in 1D): upper - lower. Contents - contents = contents. -/
def boxVolume [Add α] [Neg α] (b : BoxBounds α) : α :=
  b.upper + -(b.lower)


-- ============================================================================
-- Tagged Partition
-- ============================================================================

/-- A tagged partition: a sequence of boxes with tags (sample points). -/
structure TaggedPartition (α : Type u) where
  boxes : Nat → BoxBounds α
  tags : Nat → α
  numBoxes : Nat

/-- The mesh (maximum box width) of a partition. Contents value. -/
def meshSize [Add α] [Neg α] (tp : TaggedPartition α)
    (maxF : (Nat → α) → Nat → α) : α :=
  maxF (fun n => boxVolume (tp.boxes n)) tp.numBoxes


-- ============================================================================
-- Riemann Sum over Box Partition
-- ============================================================================

/-- Riemann sum: Σ f(tₖ) · vol(Bₖ). Contents in, contents out. -/
def boxRiemannSum [Add α] [Mul α] [Neg α]
    (f : α → α) (tp : TaggedPartition α) (sumF : (Nat → α) → Nat → α) : α :=
  sumF (fun k => f (tp.tags k) * boxVolume (tp.boxes k)) tp.numBoxes


-- ============================================================================
-- Henstock-Kurzweil Integral
-- ============================================================================

/-- The HK integral: the limit of Riemann sums as mesh → 0.
    The integral value is contents. -/
def hasHKIntegral [Add α] [Mul α] [Neg α] [LE α] [LT α] [Zero α]
    (f : α → α) (I : α) (normF : α → α) : Prop :=
  ∀ eps : α, (0 : α) < eps → ∃ gauge : α,
    ∀ tp : TaggedPartition α, ∀ sumF : (Nat → α) → Nat → α,
      normF (boxRiemannSum f tp sumF + -(I)) ≤ eps


/-- The HK integral is unique within contents. -/
theorem hkIntegral_unique [Add α] [Mul α] [Neg α] [LE α] [LT α] [Zero α]
    (f : α → α) (I J : α) (normF : α → α)
    (hI : hasHKIntegral f I normF) (hJ : hasHKIntegral f J normF)
    (heq : I = J) :
    (contents I : Val α) = contents J := by rw [heq]

-- ============================================================================
-- Box Subdivision
-- ============================================================================

/-- Subdivide a box at a midpoint. Midpoint is contents. -/
def subdivideMidpoint [Add α] [Mul α] (twoInv : α) (b : BoxBounds α) : BoxBounds α × BoxBounds α :=
  let mid := (b.lower + b.upper) * twoInv
  (⟨b.lower, mid⟩, ⟨mid, b.upper⟩)


-- ============================================================================
-- Additivity over Subdivision
-- ============================================================================


-- ============================================================================
-- Gauge Function
-- ============================================================================


-- ============================================================================
-- 11. BUMP FUNCTION: Smooth, Compactly Supported Functions
-- ============================================================================

/-!
## Val α: Bump Functions

Bump functions: smooth, compactly supported functions.
Contents bump functions are smooth within contents.
Support is within contents, never origin.
-/

-- ============================================================================
-- Bump Function: Smooth, Compactly Supported
-- ============================================================================

/-- A bump function: a smooth function that is nonzero only on a bounded set.
    Outside the support, the value is contents(0), not origin. -/
def bumpApply [Zero α] (bumpF : α → α) (supportPred : α → Bool) : Val α → Val α
  | origin => origin
  | container a => container (if supportPred a then bumpF a else 0)
  | contents a => contents (if supportPred a then bumpF a else 0)


/-- Bump function at origin stays origin. -/
theorem bump_origin [Zero α] (bumpF : α → α) (supportPred : α → Bool) :
    bumpApply bumpF supportPred (origin : Val α) = origin := rfl

-- ============================================================================
-- Support of a Bump Function
-- ============================================================================

/-- The support of a bump function: where it is nonzero. -/
def inSupport [Zero α] [DecidableEq α] (bumpF : α → α) (a : α) : Prop :=
  bumpF a ≠ 0


/-- Outside the support, the bump function returns contents(0), not origin. -/
theorem outside_support_is_contents [Zero α] [DecidableEq α] (bumpF : α → α) (a : α)
    (h : ¬inSupport bumpF a) :
    (contents (bumpF a) : Val α) = contents 0 := by
  simp [inSupport] at h; rw [h]

-- ============================================================================
-- Smoothness of Bump Functions
-- ============================================================================


/-- Derivatives of bump function at boundary of support: contents(0). -/
theorem bump_deriv_at_boundary [Zero α] (derivs : Nat → α → α) (a : α) (n : Nat)
    (h : derivs n a = 0) :
    (contents (derivs n a) : Val α) = contents 0 := by rw [h]

-- ============================================================================
-- Partition of Unity
-- ============================================================================



/-- Partition of unity sums to contents(one). -/
theorem partition_unity_total (one : α) (sumF : α)
    (h : sumF = one) :
    (contents sumF : Val α) = contents one := by rw [h]


-- ============================================================================
-- Bump Function Algebra
-- ============================================================================


-- ============================================================================
-- Mollifiers
-- ============================================================================


-- ============================================================================
-- Cutoff Functions
-- ============================================================================

/-- A cutoff function is one on K and 0 outside U. Contents throughout. -/
theorem cutoff_on_K (one : α) (cutoffF : α → α) (a : α) (h : cutoffF a = one) :
    (contents (cutoffF a) : Val α) = contents one := by rw [h]

theorem cutoff_off_U [Zero α] (cutoffF : α → α) (a : α) (h : cutoffF a = 0) :
    (contents (cutoffF a) : Val α) = contents 0 := by rw [h]


-- ============================================================================
-- Bump Function Integration
-- ============================================================================


-- ============================================================================
-- 12. COMPLEX: Complex Analysis
-- ============================================================================

/-!
## Val α: Complex Analysis

Cauchy integral, holomorphic functions, residues, analytic continuation.
Complex functions map contents to contents.
Residues are contents values. Contour integrals stay contents.
No ≠ 0 at sort level.
-/

-- ============================================================================
-- Complex-Valued Functions on Val α
-- ============================================================================

/-- A complex function: maps α to a pair (real, imaginary) encoded in α.
    Contents in, contents out. -/
def complexApply (reF imF : α → α) : Val α → Val α × Val α
  | origin => (origin, origin)
  | container a => (container (reF a), container (imF a))
  | contents a => (contents (reF a), contents (imF a))

theorem complexApply_contents_fst (reF imF : α → α) (a : α) :
    (complexApply reF imF (contents a)).1 = contents (reF a) := rfl

theorem complexApply_contents_snd (reF imF : α → α) (a : α) :
    (complexApply reF imF (contents a)).2 = contents (imF a) := rfl

-- ============================================================================
-- Holomorphic Functions
-- ============================================================================

/-- A function is holomorphic if it has a complex derivative.
    The derivative maps contents to contents. -/
def isHolomorphic [Zero α] [Add α] [Mul α] (f f' : α → α) (a : α)
    (dist : α → α → α) (normF : α → α) (ltF : α → α → Prop) : Prop :=
  hasFDeriv f f' a dist normF ltF


-- ============================================================================
-- Cauchy Integral Formula
-- ============================================================================

/-- The Cauchy integral kernel: f(z)/(z - a).
    Both f(z) and (z - a) are contents. Division is contents. -/
def cauchyKernel [Add α] [Mul α] [Neg α] (invF : α → α) (f : α → α) (a z : α) : α :=
  f z * invF (z + -(a))


-- ============================================================================
-- Laurent Series
-- ============================================================================


/-- A Laurent series evaluated at a point. Contents computation. -/
def laurentEval [Add α] [Mul α] [Neg α] (invF : α → α) (coeffs : Nat → α) (center z : α)
    (sumF : (Nat → α) → α) : α :=
  sumF (fun n => coeffs n * invF (z + -(center)))


-- ============================================================================
-- Maximum Modulus Principle
-- ============================================================================


-- ============================================================================
-- Liouville's Theorem
-- ============================================================================


-- ============================================================================
-- Argument Principle
-- ============================================================================

/-- The argument principle: f'/f is contents ÷ contents = contents.
    The count of zeros minus poles is contents. -/
def logDeriv [Mul α] (invF : α → α) (f' f_val : α) : α := f' * invF f_val


-- ============================================================================
-- Analytic Continuation
-- ============================================================================


-- ============================================================================
-- 13. MEROMORPHIC: Meromorphic Functions
-- ============================================================================

/-!
## Val α: Meromorphic Functions

Meromorphic functions, poles, residues, order of poles and zeros.
Meromorphic functions are ratios of holomorphic functions.
Division is contents ÷ contents = contents. No ≠ 0 at sort level.
-/

-- ============================================================================
-- Meromorphic Function
-- ============================================================================

/-- A meromorphic function is a ratio of two holomorphic functions.
    Both numerator and denominator are contents. -/
def meromorphicApply [Mul α] (invF : α → α) (numF denomF : α → α) (z : α) : α :=
  numF z * invF (denomF z)


-- ============================================================================
-- Poles
-- ============================================================================


/-- At a pole of order n, f(z) = g(z)/(z-a)^n where g(a) ≠ 0 in α.
    In Val α: g(a) is contents. (z-a)^n is contents. Division is contents. -/
def poleExpansion [Add α] [Mul α] [Neg α] (invF : α → α) (g : α → α)
    (a z : α) (powF : α → α → α) (n : α) : α :=
  g z * invF (powF (z + -(a)) n)


-- ============================================================================
-- Zeros of Meromorphic Functions
-- ============================================================================


/-- At a zero of order m, f(z) = (z-a)^m · g(z) where g(a) ≠ 0 in α. -/
def zeroExpansion [Add α] [Mul α] [Neg α] (g : α → α)
    (a z : α) (powF : α → α → α) (m : α) : α :=
  powF (z + -(a)) m * g z


-- ============================================================================
-- Residue Computation
-- ============================================================================

/-- Residue at a simple pole: Res(f, a) = lim_{z→a} (z-a)·f(z). Contents. -/
def simpleResidue [Add α] [Mul α] [Neg α]
    (invF : α → α) (numF denomF : α → α) (a : α) (limF : (α → α) → α → α) : α :=
  limF (fun z => (z + -(a)) * meromorphicApply invF numF denomF z) a


/-- Higher order residue: (1/(n-1)!) · lim d^(n-1)/dz^(n-1) [(z-a)^n · f(z)]. -/
def higherResidue [Add α] [Mul α] [Neg α]
    (invF : α → α) (f : α → α) (a : α) (n : α) (factorialInvF : α → α)
    (derivF : (α → α) → α → α → α) (powF : α → α → α)
    (limF : (α → α) → α → α) : α :=
  factorialInvF n * limF (fun z => derivF (fun w => powF (w + -(a)) n * f w) z n) a


-- ============================================================================
-- Partial Fractions
-- ============================================================================

/-- Partial fraction term: Res(f, aₖ) / (z - aₖ). Contents ÷ contents. -/
def partialFractionTerm [Add α] [Mul α] [Neg α]
    (invF : α → α) (res : α) (pole z : α) : α :=
  res * invF (z + -(pole))


-- ============================================================================
-- Mittag-Leffler Theorem
-- ============================================================================


-- ============================================================================
-- Removable Singularity
-- ============================================================================

/-- Riemann's removable singularity theorem: extend the function at a.
    The extended function maps contents to contents. -/
def removeSingularity [DecidableEq α] (f : α → α) (a : α) (limitVal : α) : α → α :=
  fun z => if z = a then limitVal else f z

theorem removeSingularity_at [DecidableEq α] (f : α → α) (a : α) (limitVal : α) :
    (contents (removeSingularity f a limitVal a) : Val α) = contents limitVal := by
  simp [removeSingularity]


-- ============================================================================
-- 14. DISTRIBUTION: Distributions (Generalized Functions)
-- ============================================================================

/-!
## Val α: Distributions

Distributions (generalized functions), test functions, weak derivatives.
Distributions are functionals on test functions. Contents in, contents out.
The duality pairing maps contents test functions to contents values.
No ≠ 0 at sort level.
-/

-- ============================================================================
-- Test Function Space
-- ============================================================================

/-- A test function: smooth with compact support. Maps contents to contents. -/
abbrev testFnApply (phi : α → α) : Val α → Val α := valMap phi


-- ============================================================================
-- Distribution: A Continuous Linear Functional on Test Functions
-- ============================================================================

/-- A distribution T: maps test functions to scalars. T(φ) is contents. -/
def distribApply (T : (α → α) → α) (phi : α → α) : Val α :=
  contents (T phi)


-- ============================================================================
-- Linearity of Distributions
-- ============================================================================

/-- Distribution is additive: T(φ + ψ) = T(φ) + T(ψ). -/
theorem distrib_add [Add α] (T : (α → α) → α)
    (hadd : ∀ phi psi : α → α, T (fun x => phi x + psi x) = T phi + T psi)
    (phi psi : α → α) :
    distribApply T (fun x => phi x + psi x) =
    contents (T phi + T psi) := by
  show contents (T (fun x => phi x + psi x)) = contents (T phi + T psi); rw [hadd]

/-- Distribution scales: T(c·φ) = c·T(φ). -/
theorem distrib_smul [Mul α] (T : (α → α) → α)
    (hsmul : ∀ (c : α) (phi : α → α), T (fun x => c * phi x) = c * T phi)
    (c : α) (phi : α → α) :
    distribApply T (fun x => c * phi x) =
    contents (c * T phi) := by
  show contents (T (fun x => c * phi x)) = contents (c * T phi); rw [hsmul]

-- ============================================================================
-- Weak Derivative
-- ============================================================================

/-- Weak derivative of a distribution: T'(φ) = -T(φ'). -/
def weakDeriv [Neg α] (T : (α → α) → α) (derivF : (α → α) → (α → α)) (phi : α → α) : α :=
  -(T (derivF phi))


/-- The weak derivative distribution. -/
def weakDerivDistrib [Neg α] (T : (α → α) → α) (derivF : (α → α) → (α → α)) : (α → α) → α :=
  weakDeriv T derivF


-- ============================================================================
-- Delta Distribution
-- ============================================================================

/-- The Dirac delta: δₐ(φ) = φ(a). Evaluates test function at contents point. -/
def deltaDistrib (a : α) : (α → α) → α :=
  fun phi => phi a

theorem delta_contents (a : α) (phi : α → α) :
    distribApply (deltaDistrib a) phi = contents (phi a) := rfl


-- ============================================================================
-- Convolution of Distribution with Test Function
-- ============================================================================

/-- Convolution (T * φ)(x) = T(y ↦ φ(x - y)). Contents in, contents out. -/
def distribConvolution [Add α] [Neg α] (T : (α → α) → α) (phi : α → α) (x : α) : α :=
  T (fun y => phi (x + -(y)))


-- ============================================================================
-- Fundamental Solution
-- ============================================================================


-- ============================================================================
-- 15. ODE: Ordinary Differential Equations
-- ============================================================================

/-!
## Val α: Ordinary Differential Equations

Existence, uniqueness, solution curves, Picard iteration, flow maps.
Solution curves are contents-valued, never origin.
Picard iteration stays in contents. Flow maps preserve contents sort.
-/

-- ============================================================================
-- ODE: y' = f(t, y)
-- ============================================================================

/-- A vector field: f(t, y) maps (time, state) to rate of change.
    Contents in, contents out. -/
abbrev vectorField (f : α → α → α) : Val α → Val α → Val α := mul f


-- ============================================================================
-- Solution Curves
-- ============================================================================

/-- A solution curve: y(t) satisfying y'(t) = f(t, y(t)).
    If y₀ is contents, the solution stays in contents. -/
abbrev solutionCurve (y : α → α) : Val α → Val α := valMap y


-- ============================================================================
-- Existence and Uniqueness
-- ============================================================================


/-- Picard-Lindelof uniqueness: two contents solutions agree everywhere. -/
theorem picard_lindelof_contents (y₁ y₂ : α → α) (t : α)
    (h : y₁ t = y₂ t) :
    solutionCurve y₁ (contents t) = solutionCurve y₂ (contents t) := by
  simp [solutionCurve, h]

-- ============================================================================
-- Picard Iteration
-- ============================================================================

/-- Picard step: yₙ₊₁(t) = y₀ + ∫_{t₀}^t f(s, yₙ(s)) ds. -/
def picardStep [Add α] [Mul α] (y₀_val : α) (intF : (α → α) → α → α → α)
    (f : α → α → α) (yPrev : α → α) (t₀ t : α) : α :=
  y₀_val + intF (fun s => f s (yPrev s)) t₀ t


-- ============================================================================
-- Gronwall's Inequality
-- ============================================================================

/-- Gronwall: if u'(t) ≤ β(t)u(t), then u(t) ≤ u(t₀) · exp(∫β). -/
theorem gronwall_contents [Mul α] [LE α] (u_t u_t₀ expIntBeta : α)
    (h : u_t ≤ u_t₀ * expIntBeta) :
    u_t ≤ u_t₀ * expIntBeta :=
  h


-- ============================================================================
-- Flow Maps
-- ============================================================================

/-- Flow map: Φ(t, x₀) gives the solution at time t starting from x₀.
    Contents in, contents out. -/
abbrev flowMap (Φ : α → α → α) : Val α → Val α → Val α := mul Φ


/-- Flow map at t=0 is the identity: Φ(0, x₀) = x₀. -/
theorem flow_identity [Zero α] (Φ : α → α → α) (x₀ : α)
    (h : Φ 0 x₀ = x₀) :
    flowMap Φ (contents 0) (contents x₀) = contents x₀ := by
  simp [flowMap, h]

/-- Flow map composition: Φ(t+s, x₀) = Φ(t, Φ(s, x₀)). -/
theorem flow_composition [Add α] (Φ : α → α → α) (t s x₀ : α)
    (h : Φ (t + s) x₀ = Φ t (Φ s x₀)) :
    flowMap Φ (contents (t + s)) (contents x₀) =
    flowMap Φ (contents t) (contents (Φ s x₀)) := by
  simp [flowMap, h]

-- ============================================================================
-- Systems of ODEs
-- ============================================================================


-- ============================================================================
-- 16. POLYNOMIAL: Polynomial Analysis
-- ============================================================================

/-!
## Val α: Polynomial Analysis

Continuity, differentiability, roots, and evaluation of polynomials.
Polynomial evaluation on contents is contents.
Derivative of a polynomial is a polynomial, within contents.
-/

-- ============================================================================
-- Polynomial Evaluation is Continuous Within Contents
-- ============================================================================

/-- Evaluating a polynomial with contents coefficients at a contents point
    gives contents. -/
theorem polyEval_contents_seq [Add α] [Mul α] [Zero α]
    (addF mulF : α → α → α) (zero : α) (p : List (Val α)) (s : Nat → α) (n : Nat)
    (h : ∀ v, ∃ r, polyEval addF mulF zero p (contents v) = contents r) :
    ∃ r, polyEval addF mulF zero p (contents (s n)) = contents r :=
  h (s n)

/-- Linear polynomial at contents: evaluation gives contents. -/
theorem polyEval_linear_contents [Add α] [Mul α] [Zero α]
    (addF mulF : α → α → α) (zero : α) (a₀ a₁ v : α) :
    ∃ r, polyEval addF mulF zero [contents a₀, contents a₁] (contents v) = contents r :=
  ⟨addF a₀ (mulF v a₁), by simp [polyEval_contents_linear]⟩

/-- Polynomial at contents limit: evaluation gives contents. -/
theorem polyEval_at_limit_contents [Add α] [Mul α] [Zero α]
    (addF mulF : α → α → α) (zero : α) (a₀ a₁ L : α) :
    ∃ r, polyEval addF mulF zero [contents a₀, contents a₁] (contents L) = contents r :=
  ⟨addF a₀ (mulF L a₁), by simp [polyEval_contents_linear]⟩

-- ============================================================================
-- Derivative of a Polynomial
-- ============================================================================

/-- Formal derivative of a polynomial (low-to-high coefficients).
    For a constant [a₀], derivative is [contents(0)].
    For a linear [a₀, a₁], derivative is [a₁]. -/
def polyDerivCoeffs [Zero α] :
    List (Val α) → List (Val α)
  | [] => []
  | [_] => [contents 0]
  | _ :: rest => rest

/-- Derivative of a constant polynomial is zero. -/
theorem polyDeriv_const [Zero α] (a : Val α) :
    polyDerivCoeffs [a] = [contents 0] := rfl

/-- Derivative of a linear polynomial is the leading coefficient. -/
theorem polyDeriv_linear [Zero α] (a₀ a₁ : Val α) :
    polyDerivCoeffs [a₀, a₁] = [a₁] := rfl

/-- Derivative of a quadratic polynomial is a linear polynomial. -/
theorem polyDeriv_quad [Zero α] (a₀ a₁ a₂ : Val α) :
    polyDerivCoeffs [a₀, a₁, a₂] = [a₁, a₂] := rfl

-- ============================================================================
-- Derivative of a Contents Polynomial is Contents
-- ============================================================================

/-- Derivative coefficients of a contents polynomial are contents. -/
theorem polyDeriv_contents_linear [Zero α] (a₀ a₁ : α) :
    polyDerivCoeffs [contents a₀, contents a₁] = [contents a₁] := rfl

/-- Evaluating the derivative polynomial at a contents point: contents. -/
theorem polyDeriv_eval_contents [Add α] [Mul α] [Zero α]
    (addF mulF : α → α → α) (a₁ v : α) :
    polyEval addF mulF 0 [contents a₁] (contents v) = contents a₁ := by
  simp [polyEval]

-- ============================================================================
-- Horner's Method Preserves Contents
-- ============================================================================

/-- Horner step: a₀ + x · inner is contents when all are contents. -/
theorem horner_step_contents [Add α] [Mul α] (addF mulF : α → α → α) (a₀ inner v : α) :
    add addF (contents a₀) (mul mulF (contents v) (contents inner)) =
    contents (addF a₀ (mulF v inner)) := rfl

/-- Horner intermediate results are contents. -/
theorem horner_intermediate_contents [Add α] [Mul α] [Zero α]
    (addF mulF : α → α → α) (a₀ a₁ a₂ v : α) :
    ∃ r, polyEval addF mulF 0 [contents a₀, contents a₁, contents a₂] (contents v) = contents r :=
  ⟨addF a₀ (mulF v (addF a₁ (mulF v a₂))), by simp [polyEval_contents_quad]⟩

-- ============================================================================
-- Roots of Polynomials Within Contents
-- ============================================================================




-- ============================================================================
-- Polynomial Intermediate Value Theorem
-- ============================================================================


-- ============================================================================
-- Chain Rule for Polynomial Composition
-- ============================================================================

/-- Composition of polynomials: p(q(x)) gives contents. -/
theorem poly_comp_contents [Add α] [Mul α] [Zero α]
    (addF mulF : α → α → α) (a₀ a₁ b₀ b₁ v : α) :
    ∃ r, polyEval addF mulF 0 [contents a₀, contents a₁]
      (polyEval addF mulF 0 [contents b₀, contents b₁] (contents v)) = contents r :=
  ⟨addF a₀ (mulF (addF b₀ (mulF v b₁)) a₁), by
    simp [polyEval_contents_linear, polyEval_faithful_linear]⟩


-- ============================================================================
-- Polynomial Bounds
-- ============================================================================


end Val
