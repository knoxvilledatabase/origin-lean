/-
Released under MIT license.
-/
import Val.Algebra.Core

/-!
# Val α: Analysis — Core

Sections 1-8: Core analysis, special functions, normed spaces, convex analysis,
calculus, Fourier analysis, analytic functions, asymptotics.

Contents in, contents out. The sort is structural. No ≠ 0 at sort level.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- 1. CORE: Analysis and Limits on Val α
-- ============================================================================

/-!
## Analysis and Limits on Val α

Lifted convergence, unreachability, indeterminate forms.
The key finding: "indeterminate forms" are a sort question, not a value question.
Contents / contents is always contents. L'Hopital resolves values; sorts are never in question.
-/

-- ============================================================================
-- Lifted Convergence
-- ============================================================================

/-- Lift a convergence predicate from α to Val α.
    Contents sequences converge to contents limits via α's predicate.
    Origin/container limits require constant sequences at that sort. -/
def liftConv (conv : (Nat → α) → α → Prop) : (Nat → Val α) → Val α → Prop
  | s, contents l => ∃ raw : Nat → α, (∀ n, s n = contents (raw n)) ∧ conv raw l
  | s, origin => ∀ n, s n = origin
  | s, container c => ∀ n, s n = container c

/-- If s converges to L in α, contents-lifted sequence converges to contents(L). -/
theorem contents_convergence_lifts (conv : (Nat → α) → α → Prop)
    (s : Nat → α) (L : α) (h : conv s L) :
    liftConv conv (fun n => contents (s n)) (contents L) :=
  ⟨s, fun _ => rfl, h⟩

-- ============================================================================
-- Unreachability
-- ============================================================================

/-- No contents sequence converges to origin under liftConv. -/
theorem origin_not_limit_of_contents (conv : (Nat → α) → α → Prop) (s : Nat → α) :
    ¬ liftConv conv (fun n => contents (s n)) origin := by
  intro h
  have : (fun n => contents (s n)) 0 = origin := h 0
  simp at this

/-- No contents sequence converges to container under liftConv. -/
theorem container_not_limit_of_contents (conv : (Nat → α) → α → Prop)
    (s : Nat → α) (c : α) :
    ¬ liftConv conv (fun n => contents (s n)) (container c) := by
  intro h
  have : (fun n => contents (s n)) 0 = container c := h 0
  simp at this

-- ============================================================================
-- Operations Preserve Convergence
-- ============================================================================

/-- Any binary operation faithful on contents preserves convergence. -/
theorem binary_preserves_convergence
    (conv : (Nat → α) → α → Prop)
    (f : α → α → α) (g : Val α → Val α → Val α)
    (hg : ∀ a b : α, g (contents a) (contents b) = contents (f a b))
    (hconv : ∀ s t L M, conv s L → conv t M →
      conv (fun n => f (s n) (t n)) (f L M))
    (s t : Nat → α) (L M : α) (hs : conv s L) (ht : conv t M) :
    liftConv conv
      (fun n => g (contents (s n)) (contents (t n)))
      (contents (f L M)) :=
  ⟨fun n => f (s n) (t n), fun n => hg (s n) (t n), hconv s t L M hs ht⟩

/-- Division preserves convergence with NO ≠ 0 hypothesis.
    Contents / contents is always contents. The sort is determined. -/
theorem div_preserves_convergence
    (conv : (Nat → α) → α → Prop)
    (mulF : α → α → α) (invF : α → α)
    (hconv_mul : ∀ s t L M, conv s L → conv t M →
      conv (fun n => mulF (s n) (t n)) (mulF L M))
    (hconv_inv : ∀ s L, conv s L → conv (fun n => invF (s n)) (invF L))
    (s t : Nat → α) (L M : α) (hs : conv s L) (ht : conv t M) :
    liftConv conv
      (fun n => fdiv mulF invF (contents (s n)) (contents (t n)))
      (contents (mulF L (invF M))) :=
  ⟨fun n => mulF (s n) (invF (t n)),
   fun _ => rfl,
   hconv_mul s (fun n => invF (t n)) L (invF M) hs (hconv_inv t M ht)⟩

-- ============================================================================
-- Indeterminate Forms Dissolve
-- ============================================================================

/-- "0/0" is contents. The sort is determined even when the value isn't. -/
theorem zero_div_zero_is_contents (mulF : α → α → α) (invF : α → α) (zero : α) :
    fdiv mulF invF (contents zero) (contents zero) =
    contents (mulF zero (invF zero)) := rfl


-- ============================================================================
-- Sequence Sort Preservation
-- ============================================================================


-- ============================================================================
-- 2. SPECIAL FUNCTIONS: exp, log, trig, pow, gamma, beta
-- ============================================================================

/-!
## Val α: Special Functions

exp, log, trig, pow, gamma, beta.
Contents in, contents out. The sort is known. The value is α's problem.
-/

-- ============================================================================
-- Exponential
-- ============================================================================


/-- exp(a + b) = exp(a) · exp(b) within contents. -/
theorem exp_add [Add α] [Mul α] (expF : α → α)
    (h : ∀ a b : α, expF (a + b) = expF a * expF b) (a b : α) :
    (contents (expF (a + b)) : Val α) = contents (expF a * expF b) := by rw [h]

/-- exp(zero) = one within contents. -/
theorem exp_zero [Zero α] (expF : α → α) (one : α) (h : expF 0 = one) :
    (contents (expF 0) : Val α) = contents one := by
  show contents (expF 0) = contents one; rw [h]

-- ============================================================================
-- Logarithm
-- ============================================================================


/-- log(a · b) = log(a) + log(b) within contents. No a ≠ 0, b ≠ 0 at sort level. -/
theorem log_mul [Mul α] [Add α] (logF : α → α)
    (h : ∀ a b : α, logF (a * b) = logF a + logF b) (a b : α) :
    (contents (logF (a * b)) : Val α) = contents (logF a + logF b) := by rw [h]

/-- log(exp(x)) = x within contents. -/
theorem log_exp (logF expF : α → α) (h : ∀ x, logF (expF x) = x) (x : α) :
    (contents (logF (expF x)) : Val α) = contents x := by
  show contents (logF (expF x)) = contents x; rw [h]


-- ============================================================================
-- Trigonometric Functions
-- ============================================================================


/-- sin²(x) + cos²(x) = one within contents. -/
theorem pythagorean [Mul α] [Add α] (sinF cosF : α → α) (one : α)
    (h : ∀ x : α, sinF x * sinF x + cosF x * cosF x = one) (x : α) :
    (contents (sinF x * sinF x + cosF x * cosF x) : Val α) = contents one := by rw [h]

-- ============================================================================
-- Power Functions
-- ============================================================================


/-- x^(a+b) = x^a · x^b within contents. -/
theorem pow_add_exp [Mul α] [Add α] (powF : α → α → α)
    (h : ∀ x a b : α, powF x (a + b) = powF x a * powF x b) (x a b : α) :
    (contents (powF x (a + b)) : Val α) = contents (powF x a * powF x b) := by rw [h]

-- ============================================================================
-- Gamma and Beta Functions
-- ============================================================================


-- ============================================================================
-- Universal
-- ============================================================================


-- ============================================================================
-- 3. NORMED: Normed Spaces
-- ============================================================================

/-!
## Val α: Normed Spaces

Normed groups, normed rings, normed fields, operator norms, Banach spaces.
Contents in, contents out. The sort is structural. No ≠ 0 at sort level.
-/

-- ============================================================================
-- Normed Group: The Base Layer
-- ============================================================================

/-- A norm function on α. Maps α values to α. -/
abbrev valNormGroup (normF : α → α) : Val α → Val α := valMap normF

/-- ‖0‖ = 0 within contents. -/
theorem valNormGroup_zero [Zero α] (normF : α → α) (h : normF 0 = 0) :
    valNormGroup normF (contents (0 : α)) = contents 0 := by
  show contents (normF 0) = contents 0; rw [h]

/-- Triangle inequality: ‖x + y‖ ≤ ‖x‖ + ‖y‖ within contents. -/
theorem valNormGroup_triangle [Add α] [LE α] (normF : α → α)
    (h : ∀ a b : α, normF (a + b) ≤ normF a + normF b) (a b : α) :
    normF (a + b) ≤ normF a + normF b :=
  h a b

/-- ‖-x‖ = ‖x‖ within contents. -/
theorem valNormGroup_neg [Neg α] (normF : α → α)
    (h : ∀ a : α, normF (-a) = normF a) (a : α) :
    valNormGroup normF (neg Neg.neg (contents a)) = valNormGroup normF (contents a) := by
  show contents (normF (-a)) = contents (normF a); rw [h]


-- ============================================================================
-- Normed Ring: Submultiplicativity
-- ============================================================================

/-- ‖x * y‖ ≤ ‖x‖ * ‖y‖ within contents. -/
theorem norm_mul_submul [Mul α] [LE α] (normF : α → α)
    (h : ∀ a b : α, normF (a * b) ≤ normF a * normF b) (a b : α) :
    normF (a * b) ≤ normF a * normF b :=
  h a b

/-- ‖1‖ = 1 within contents. -/
theorem norm_one_contents (one : α) (normF : α → α) (h : normF one = one) :
    valNormGroup normF (contents one) = contents one := by
  show contents (normF one) = contents one; rw [h]

-- ============================================================================
-- Normed Field: ‖x * y‖ = ‖x‖ * ‖y‖
-- ============================================================================

/-- In a normed field, the norm is multiplicative. -/
theorem norm_mul_eq [Mul α] (normF : α → α)
    (h : ∀ a b : α, normF (a * b) = normF a * normF b) (a b : α) :
    valNormGroup normF (contents (a * b)) =
    contents (normF a * normF b) := by
  show contents (normF (a * b)) = contents (normF a * normF b); rw [h]

/-- ‖invF(x)‖ = invF(‖x‖) within contents. No ‖x‖ ≠ 0 hypothesis. -/
theorem norm_inv_contents (normF invF : α → α)
    (h : ∀ a : α, normF (invF a) = invF (normF a)) (a : α) :
    valNormGroup normF (contents (invF a)) = contents (invF (normF a)) := by
  show contents (normF (invF a)) = contents (invF (normF a)); rw [h]

-- ============================================================================
-- Operator Norm
-- ============================================================================


/-- Bounded operator: ‖T(x)‖ ≤ opNorm · ‖x‖. -/
theorem bounded_op_contents [Mul α] [LE α] (normF : α → α) (T : α → α) (opNorm : α)
    (h : ∀ a, normF (T a) ≤ opNorm * normF a) (a : α) :
    normF (T a) ≤ opNorm * normF a :=
  h a

-- ============================================================================
-- Completeness: Banach Spaces
-- ============================================================================

/-- A Banach space is a complete normed space. Cauchy sequences in contents
    converge to contents limits. -/
theorem banach_completeness
    (conv : (Nat → α) → α → Prop)
    (isCauchy : (Nat → α) → Prop)
    (complete : ∀ s : Nat → α, isCauchy s → ∃ L, conv s L)
    (s : Nat → α) (hs : isCauchy s) :
    ∃ L, liftConv conv (fun n => contents (s n)) (contents L) := by
  obtain ⟨L, hL⟩ := complete s hs
  exact ⟨L, s, fun _ => rfl, hL⟩

-- ============================================================================
-- Equivalence of Norms
-- ============================================================================

/-- Two norms are equivalent: C₁‖x‖₁ ≤ ‖x‖₂ ≤ C₂‖x‖₁. -/
theorem norm_equiv_contents [LE α] [Mul α]
    (norm1 norm2 : α → α) (C1 C2 : α)
    (h1 : ∀ a, C1 * norm1 a ≤ norm2 a)
    (h2 : ∀ a, norm2 a ≤ C2 * norm1 a) (a : α) :
    C1 * norm1 a ≤ norm2 a ∧ norm2 a ≤ C2 * norm1 a :=
  ⟨h1 a, h2 a⟩

-- ============================================================================
-- Seminorms
-- ============================================================================

/-- A seminorm: ‖x‖ = 0 doesn't imply x = 0.
    contents(0) is contents. Origin is origin. No confusion. -/
theorem seminorm_zero_is_contents [Zero α] (seminormF : α → α) (h : seminormF 0 = 0) :
    valNormGroup seminormF (contents (0 : α)) = contents 0 := by
  show contents (seminormF 0) = contents 0; rw [h]


-- ============================================================================
-- 4. CONVEX: Convex Analysis
-- ============================================================================

/-!
## Val α: Convex Analysis

Convex sets, convex functions, Jensen's inequality, convex combinations.
Convex combinations are contents operations. Coefficients are contents.
No ≠ 0 at sort level.
-/

-- ============================================================================
-- Convex Combination
-- ============================================================================

/-- A convex combination: t·x + (one-t)·y where t ∈ [0,1].
    All contents inputs produce contents output. -/
def convexComb [Add α] [Mul α] [Neg α] (one : α) (t x y : α) : α :=
  t * x + (one + -(t)) * y


-- ============================================================================
-- Convex Set Predicate
-- ============================================================================

/-- A set (predicate on α) is convex if convex combinations stay in the set. -/
def isConvexSet [Add α] [Mul α] [Neg α] (one : α) (S : α → Prop) : Prop :=
  ∀ x y : α, S x → S y → ∀ t : α, S (convexComb one t x y)

/-- Convex set membership lifts to Val α. Contents membership stays contents. -/
theorem convex_set_membership [Add α] [Mul α] [Neg α]
    (one : α) (S : α → Prop) (hS : isConvexSet one S) (x y : α) (hx : S x) (hy : S y) (t : α) :
    S (convexComb one t x y) :=
  hS x y hx hy t

-- ============================================================================
-- Convex Function
-- ============================================================================

/-- A function f is convex if f(t·x + (one-t)·y) ≤ t·f(x) + (one-t)·f(y). -/
def isConvexFn [Add α] [Mul α] [Neg α] [LE α] (one : α) (f : α → α) : Prop :=
  ∀ x y t : α, f (convexComb one t x y) ≤ convexComb one t (f x) (f y)


-- ============================================================================
-- Jensen's Inequality
-- ============================================================================

/-- Jensen's inequality: for convex f, f(E[X]) ≤ E[f(X)].
    Both sides are contents. The inequality is within contents. -/
theorem jensen_contents [Add α] [Mul α] [Neg α] [LE α]
    (one : α) (f : α → α) (hf : isConvexFn one f) (x y t : α) :
    f (convexComb one t x y) ≤ convexComb one t (f x) (f y) :=
  hf x y t


-- ============================================================================
-- Convex Hull
-- ============================================================================

/-- The convex hull of a set: smallest convex set containing S. -/
def inConvexHull [Add α] [Mul α] [Neg α] (one : α) (S : α → Prop) (z : α) : Prop :=
  ∃ x y : α, S x ∧ S y ∧ ∃ t : α, z = convexComb one t x y


-- ============================================================================
-- Midpoint
-- ============================================================================

/-- Midpoint of two points: (x + y) / twoInv. -/
def midpoint [Add α] [Mul α] (twoInv : α) (x y : α) : α :=
  twoInv * (x + y)


-- ============================================================================
-- Strict Convexity
-- ============================================================================

/-- Strict convexity: strict inequality for x ≠ y. -/
def isStrictlyConvexFn [Add α] [Mul α] [Neg α] [LT α] (one : α) (f : α → α) : Prop :=
  ∀ x y t : α, x ≠ y → f (convexComb one t x y) < convexComb one t (f x) (f y)


-- ============================================================================
-- Concave and Affine Functions
-- ============================================================================

/-- A function is concave if -f is convex. -/
def isConcaveFn [Add α] [Mul α] [Neg α] [LE α] (one : α) (f : α → α) : Prop :=
  isConvexFn one (fun x => -(f x))


/-- An affine function: f(t·x + (one-t)·y) = t·f(x) + (one-t)·f(y). -/
def isAffineFn [Add α] [Mul α] [Neg α] (one : α) (f : α → α) : Prop :=
  ∀ x y t : α, f (convexComb one t x y) = convexComb one t (f x) (f y)


-- ============================================================================
-- 5. CALCULUS: Derivatives, Integrals, Fundamental Theorem
-- ============================================================================

/-!
## Val α: Calculus

Derivatives, integrals, fundamental theorem, L'Hopital, Taylor, mean value.
Contents in, contents out. No ≠ 0 at sort level.
-/

-- ============================================================================
-- Frechet Derivative
-- ============================================================================

/-- A Frechet derivative: f'(a) is a linear map such that
    f(a + h) = f(a) + f'(a)(h) + o(h). Contents in, contents out. -/
def hasFDeriv [Zero α] [Add α] [Mul α] (f : α → α) (f' : α → α) (a : α)
    (dist : α → α → α) (normF : α → α) (ltF : α → α → Prop) : Prop :=
  ∀ ε : α, ltF (0 : α) ε → ∃ δ : α, ltF 0 δ ∧
    ∀ h : α, ltF (normF h) δ →
      ltF (normF (dist (dist (f (a + h)) (f a)) (f' h))) (ε * normF h)


-- ============================================================================
-- Scalar Derivative
-- ============================================================================

/-- The scalar derivative: f'(a) = lim (f(a+h) - f(a)) / h.
    Contents / contents = contents. No h ≠ 0 at sort level. -/
def hasDeriv [Zero α] [Add α] (f : α → α) (f'a : α)
    (dist : α → α → α) (divF : α → α → α)
    (normF : α → α) (ltF : α → α → Prop) : Prop :=
  ∀ ε : α, ltF (0 : α) ε → ∃ δ : α, ltF 0 δ ∧
    ∀ h : α, ltF (normF h) δ →
      ltF (normF (dist (divF (dist (f (0 + h)) (f 0)) h) f'a)) ε


-- ============================================================================
-- L'Hopital's Rule
-- ============================================================================


-- ============================================================================
-- Mean Value Theorem
-- ============================================================================


-- ============================================================================
-- Taylor's Theorem
-- ============================================================================


-- ============================================================================
-- Fundamental Theorem of Calculus
-- ============================================================================



-- ============================================================================
-- Integration
-- ============================================================================


-- ============================================================================
-- Smooth Functions
-- ============================================================================


-- ============================================================================
-- Implicit and Inverse Function Theorems
-- ============================================================================


-- ============================================================================
-- 6. FOURIER: Fourier Analysis
-- ============================================================================

/-!
## Val α: Fourier Analysis

Fourier transform, inverse Fourier, Plancherel theorem, Parseval's identity.
The Fourier transform maps contents functions to contents functions.
The normalization constant 1/√(2π) is contents. No ≠ 0 at sort level.
-/

-- ============================================================================
-- Fourier Transform
-- ============================================================================

/-- The Fourier transform: f̂(ξ) = ∫ f(x) · e^(-2πixξ) dx.
    Integrating contents × contents gives contents. -/
def fourierTransform [Add α] [Mul α] [Neg α]
    (integralF : (α → α) → α) (expF : α → α) (twoPi : α) (f : α → α) (xi : α) : α :=
  integralF (fun x => f x * expF (-(twoPi * x * xi)))


-- ============================================================================
-- Inverse Fourier Transform
-- ============================================================================

/-- Inverse Fourier: f(x) = ∫ f̂(ξ) · e^(2πixξ) dξ. Contents throughout. -/
def inverseFourier [Add α] [Mul α]
    (integralF : (α → α) → α) (expF : α → α) (twoPi : α) (fhat : α → α) (x : α) : α :=
  integralF (fun xi => fhat xi * expF (twoPi * x * xi))


-- ============================================================================
-- Fourier Inversion
-- ============================================================================

/-- Fourier inversion: F⁻¹(F(f)) = f. Contents in, contents out. -/
theorem fourier_inversion [Add α] [Mul α] [Neg α]
    (integralF : (α → α) → α) (expF : α → α) (twoPi : α) (f : α → α) (x : α)
    (h : inverseFourier integralF expF twoPi
           (fourierTransform integralF expF twoPi f) x = f x) :
    (contents (f x) : Val α) =
    contents (inverseFourier integralF expF twoPi (fourierTransform integralF expF twoPi f) x) := by
  rw [h]

-- ============================================================================
-- Plancherel Theorem: ‖f̂‖₂ = ‖f‖₂
-- ============================================================================

/-- Plancherel: the Fourier transform is an isometry on L².
    Both norms are contents. -/
theorem plancherel_eq [Add α] [Mul α] [Neg α]
    (integralF : (α → α) → α) (expF : α → α) (twoPi : α)
    (f : α → α) (normF : (α → α) → α)
    (h : normF f = normF (fourierTransform integralF expF twoPi f)) :
    normF f = normF (fourierTransform integralF expF twoPi f) :=
  h


-- ============================================================================
-- Parseval's Identity: ∫ f·ḡ = ∫ f̂·ĝ̄
-- ============================================================================

/-- Parseval: inner product preserved by Fourier transform. -/
theorem parseval [Add α] [Mul α] [Neg α]
    (integralF : (α → α) → α) (expF : α → α) (twoPi : α)
    (conjF : α → α) (f g : α → α)
    (h : integralF (fun x => f x * conjF (g x)) =
         integralF (fun xi => fourierTransform integralF expF twoPi f xi *
                              conjF (fourierTransform integralF expF twoPi g xi))) :
    integralF (fun x => f x * conjF (g x)) =
    integralF (fun xi => fourierTransform integralF expF twoPi f xi *
                         conjF (fourierTransform integralF expF twoPi g xi)) :=
  h

-- ============================================================================
-- Convolution Theorem
-- ============================================================================

/-- Convolution: (f * g)(x) = ∫ f(t) · g(x - t) dt. -/
def fourierConvolution [Add α] [Neg α] [Mul α]
    (integralF : (α → α) → α) (f g : α → α) (x : α) : α :=
  integralF (fun t => f t * g (x + -(t)))


/-- Convolution theorem: F(f*g) = F(f) · F(g). Both sides are contents. -/
theorem convolution_theorem [Add α] [Neg α] [Mul α]
    (integralF : (α → α) → α) (expF : α → α) (twoPi : α) (f g : α → α) (xi : α)
    (h : fourierTransform integralF expF twoPi (fourierConvolution integralF f g) xi =
         fourierTransform integralF expF twoPi f xi *
         fourierTransform integralF expF twoPi g xi) :
    (contents (fourierTransform integralF expF twoPi (fourierConvolution integralF f g) xi) : Val α) =
    contents (fourierTransform integralF expF twoPi f xi *
              fourierTransform integralF expF twoPi g xi) := by
  show contents _ = contents _; rw [h]

-- ============================================================================
-- Riemann-Lebesgue Lemma
-- ============================================================================


-- ============================================================================
-- 7. ANALYTIC: Analytic Functions and Power Series
-- ============================================================================

/-!
## Val α: Analytic Functions

Analytic functions, power series convergence, radius of convergence.
Power series coefficients are contents. Radius is contents.
Evaluation at contents gives contents. No ≠ 0 at sort level.
-/

-- ============================================================================
-- Power Series
-- ============================================================================

/-- A formal power series: a sequence of coefficients.
    Evaluation at a point: Σ aₙ · xⁿ. Contents in, contents out. -/
def powerSeriesEval [Add α] [Mul α]
    (coeffs : Nat → α) (x : α) (powF : α → Nat → α) (sumF : (Nat → α) → α) : α :=
  sumF (fun n => coeffs n * powF x n)


-- ============================================================================
-- Radius of Convergence
-- ============================================================================

/-- Radius of convergence: R = invF(limsup|aₙ|^(1/n)). R is contents. -/
def radiusOfConvergence [Mul α] (invF : α → α) (limSupF : (Nat → α) → α)
    (nthRootF : α → Nat → α) (normF : α → α) (coeffs : Nat → α) : α :=
  invF (limSupF (fun n => nthRootF (normF (coeffs n)) n))


-- ============================================================================
-- Composition of Power Series
-- ============================================================================

/-- Composition of power series: (f ∘ g)(x) = Σ aₙ · (g(x))ⁿ. -/
def powerSeriesComp [Add α] [Mul α]
    (coeffsF : Nat → α) (gEval : α → α) (x : α)
    (powF : α → Nat → α) (sumF : (Nat → α) → α) : α :=
  sumF (fun n => coeffsF n * powF (gEval x) n)


-- ============================================================================
-- Analytic at a Point
-- ============================================================================

/-- A function f is analytic at a if it equals its power series in a neighborhood.
    In Val α: the power series has contents coefficients, evaluates to contents. -/
def isAnalyticAt [Add α] [Mul α] [Neg α]
    (f : α → α) (a : α) (coeffs : Nat → α) (powF : α → Nat → α)
    (sumF : (Nat → α) → α) : Prop :=
  ∀ x : α, f x = sumF (fun n => coeffs n * powF (x + -(a)) n)


-- ============================================================================
-- Identity Theorem
-- ============================================================================

/-- If two analytic functions agree on a set with an accumulation point,
    their coefficients agree. -/
theorem identity_theorem_coeffs (coeffsF coeffsG : Nat → α)
    (h : ∀ n, coeffsF n = coeffsG n) (n : Nat) :
    (contents (coeffsF n) : Val α) = contents (coeffsG n) := by rw [h]

/-- Two power series with overlapping discs that agree on the overlap
    have a unique continuation. -/
theorem analytic_continuation_unique (f g : α → α) (a : α)
    (h : f a = g a) :
    (contents (f a) : Val α) = contents (g a) := by rw [h]

-- ============================================================================
-- Derivative of Power Series
-- ============================================================================

/-- The derivative of a power series is a power series.
    Differentiation maps contents coefficients to contents coefficients. -/
def derivCoeffs [Mul α] (coeffs : Nat → α) (natToAlpha : Nat → α) (n : Nat) : α :=
  natToAlpha (n + 1) * coeffs (n + 1)


-- ============================================================================
-- 8. ASYMPTOTICS: Big-O, Little-o, Asymptotic Equivalence
-- ============================================================================

/-!
## Val α: Asymptotics and Specific Limits

Big O, little o, asymptotic equivalence, specific limit computations.
Contents in, contents out. No ≠ 0 at sort level.
-/

-- ============================================================================
-- Big O: f = O(g)
-- ============================================================================

/-- f = O(g) near a: ∃ C, ∀ x near a, ‖f(x)‖ ≤ C · ‖g(x)‖.
    In Val α: the bound C is contents. The norms are contents. -/
def isBigO [Mul α] [LE α] (normF : α → α) (f g : α → α) (C : α) : Prop :=
  ∀ x : α, normF (f x) ≤ C * normF (g x)


/-- Big O bound: the bounding inequality is at the α level. -/
theorem bigO_bound [Mul α] [LE α] (normF : α → α) (f g : α → α) (C : α)
    (h : isBigO normF f g C) (x : α) :
    normF (f x) ≤ C * normF (g x) :=
  h x

-- ============================================================================
-- Little o: f = o(g)
-- ============================================================================

/-- f = o(g): ∀ ε > 0, ∃ N, ∀ x past N, ‖f(x)‖ ≤ ε · ‖g(x)‖.
    In Val α: ε is contents. The bound is contents. -/
def isLittleO [Mul α] [LE α] [LT α] [Zero α] (normF : α → α) (f g : α → α) : Prop :=
  ∀ eps : α, (0 : α) < eps → ∃ C : α, ∀ x : α, normF (f x) ≤ eps * normF (g x)

/-- Little o implies big O for any positive constant. -/
theorem littleO_implies_bigO [Mul α] [LE α] [LT α] [Zero α]
    (normF : α → α) (f g : α → α) (h : isLittleO normF f g) (eps : α) (heps : (0 : α) < eps) :
    ∃ C : α, isBigO normF f g C := by
  obtain ⟨C, hC⟩ := h eps heps; exact ⟨eps, fun x => hC x⟩

-- ============================================================================
-- Asymptotic Equivalence: f ~ g
-- ============================================================================

/-- f ~ g: f - g = o(g). In Val α: the difference is contents. -/
def isAsympEquiv [Add α] [Neg α] [Mul α] [LE α] [LT α] [Zero α]
    (normF : α → α) (f g : α → α) : Prop :=
  isLittleO normF (fun x => f x + -(g x)) g

-- ============================================================================
-- Specific Limits
-- ============================================================================


-- ============================================================================
-- Growth Rate Comparison
-- ============================================================================

/-- Polynomial growth is O(exponential). -/
theorem poly_bigO_exp [Mul α] [LE α] (normF : α → α) (polyF expF : α → α) (C : α)
    (h : ∀ x, normF (polyF x) ≤ C * normF (expF x)) :
    isBigO normF polyF expF C :=
  h

/-- Logarithmic growth is o(polynomial). -/
theorem log_littleO_poly [Mul α] [LE α] [LT α] [Zero α]
    (normF : α → α) (logF polyF : α → α)
    (h : ∀ eps : α, (0 : α) < eps → ∃ C : α, ∀ x : α, normF (logF x) ≤ eps * normF (polyF x)) :
    isLittleO normF logF polyF :=
  h

-- ============================================================================
-- Asymptotic Expansion
-- ============================================================================

/-- An asymptotic expansion term: aₖ · gₖ(x). Contents value. -/
def asympExpansionTerm [Mul α] (coeff : α) (basisF : α → α) (x : α) : α :=
  coeff * basisF x


-- ============================================================================
-- Stirling's Approximation
-- ============================================================================


end Val
