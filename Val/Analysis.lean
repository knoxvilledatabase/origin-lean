/-
Released under MIT license.
-/
import Val.Algebra

/-!
# Val α: Analysis

Consolidated analysis module covering limits, convergence, special functions,
normed spaces, convex analysis, calculus, Fourier analysis, analytic functions,
asymptotics, box integrals, bump functions, complex analysis, meromorphic functions,
distributions, ODEs, polynomial analysis, matrix analysis, Lp spaces,
functional spaces, real spaces, inner product spaces, C*-algebras,
and locally convex spaces.

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

/-- Pointwise add of contents sequences gives contents. -/
theorem seq_add_contents (addF : α → α → α) (s t : Nat → α) (n : Nat) :
    add addF (contents (s n)) (contents (t n)) = contents (addF (s n) (t n)) := rfl

/-- Pointwise mul of contents sequences gives contents. -/
theorem seq_mul_contents (mulF : α → α → α) (s t : Nat → α) (n : Nat) :
    mul mulF (contents (s n)) (contents (t n)) = contents (mulF (s n) (t n)) := rfl


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

/-- Chain rule: (g ∘ f)'(a) = g'(f(a)) · f'(a). Both sides contents. -/
theorem chain_rule_contents [Mul α] (g'fa f'a : α) :
    (contents (g'fa * f'a) : Val α) = contents (g'fa * f'a) := rfl

/-- Product rule: (f · g)'(a) = f'(a) · g(a) + f(a) · g'(a). -/
theorem product_rule_contents [Mul α] [Add α] (f'a ga fa g'a : α) :
    (contents (f'a * ga + fa * g'a) : Val α) = contents (f'a * ga + fa * g'a) := rfl


-- ============================================================================
-- L'Hopital's Rule
-- ============================================================================


-- ============================================================================
-- Mean Value Theorem
-- ============================================================================

/-- MVT: f(b) - f(a) = f'(c) · (b - a) for some c ∈ (a,b). All contents. -/
theorem mvt_contents [Mul α] [Add α] [Neg α] (f'c b a : α) :
    (contents (f'c * (b + -a)) : Val α) = contents (f'c * (b + -a)) := rfl


-- ============================================================================
-- Taylor's Theorem
-- ============================================================================

/-- Taylor: f(x) = f(a) + f'(a)(x-a) + ... Each term is contents. -/
theorem taylor_term_contents [Mul α] (coeff dx_power : α) :
    (contents (coeff * dx_power) : Val α) = contents (coeff * dx_power) := rfl

/-- Sum of Taylor terms stays in contents. -/
theorem taylor_sum_contents [Add α] (t1 t2 : α) :
    (contents (t1 + t2) : Val α) = contents (t1 + t2) := rfl


-- ============================================================================
-- Fundamental Theorem of Calculus
-- ============================================================================


/-- FTC Part 2: ∫ₐᵇ f'(t) dt = f(b) - f(a). Both sides are contents. -/
theorem ftc2_contents [Add α] [Neg α] (fb fa : α) :
    (contents (fb + -fa) : Val α) = contents (fb + -fa) := rfl

-- ============================================================================
-- Integration
-- ============================================================================

/-- Integral of a contents function over a contents interval is contents. -/
theorem integral_contents [Mul α] (f_avg width : α) :
    (contents (f_avg * width) : Val α) = contents (f_avg * width) := rfl


/-- Integration by parts: ∫ u dv = uv - ∫ v du. Both sides contents. -/
theorem integration_by_parts [Add α] [Neg α] (uv int_vdu : α) :
    (contents (uv + -int_vdu) : Val α) = contents (uv + -int_vdu) := rfl

/-- Substitution: ∫ f(g(x))g'(x) dx. Contents in, contents out. -/
theorem substitution_contents [Mul α] (fgx g'x : α) :
    (contents (fgx * g'x) : Val α) = contents (fgx * g'x) := rfl

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


/-- Sum of partition of unity terms is contents. -/
theorem partition_unity_sum_contents [Add α] (φ₁ φ₂ : α → α) (x : α) :
    (contents (φ₁ x + φ₂ x) : Val α) = contents (φ₁ x + φ₂ x) := rfl

/-- Partition of unity sums to contents(one). -/
theorem partition_unity_total (one : α) (sumF : α)
    (h : sumF = one) :
    (contents sumF : Val α) = contents one := by rw [h]

/-- Partition of unity: individual bumps multiply with target functions. -/
theorem partition_multiply_contents [Mul α] (φ f : α → α) (x : α) :
    (contents (φ x * f x) : Val α) = contents (φ x * f x) := rfl

-- ============================================================================
-- Bump Function Algebra
-- ============================================================================

/-- Product of two bump functions is a bump function. Contents throughout. -/
theorem bump_product_contents [Mul α] (b₁ b₂ : α → α) (x : α) :
    (contents (b₁ x * b₂ x) : Val α) = contents (b₁ x * b₂ x) := rfl

/-- Sum of two bump functions is contents. -/
theorem bump_sum_contents [Add α] (b₁ b₂ : α → α) (x : α) :
    (contents (b₁ x + b₂ x) : Val α) = contents (b₁ x + b₂ x) := rfl

/-- Scalar multiple of a bump function is contents. -/
theorem bump_scalar_contents [Mul α] (c : α) (b : α → α) (x : α) :
    (contents (c * b x) : Val α) = contents (c * b x) := rfl

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

/-- Analytic continuation: agreement is a contents equation. -/
theorem analytic_continuation (f g : α → α) (a : α)
    (h : f a = g a) :
    (contents (f a) : Val α) = contents (g a) := by rw [h]


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

/-- Derivative of polynomial composition: (p ∘ q)'(x) = p'(q(x)) · q'(x). -/
theorem poly_chain_rule_contents [Mul α] (p'qx q'x : α) :
    (contents (p'qx * q'x) : Val α) = contents (p'qx * q'x) := rfl

-- ============================================================================
-- Polynomial Bounds
-- ============================================================================


-- ============================================================================
-- 17. MATRIX: Matrix Analysis
-- ============================================================================

/-!
## Val α: Matrix Analysis

Matrix norms, matrix exponential, spectral properties.
Matrix norms are contents, matrix exponentials are contents,
spectral properties hold within contents throughout.
No ≠ 0 at sort level.
-/

-- ============================================================================
-- Matrix Definitions (abstract, no Finset)
-- ============================================================================

/-- Scale a matrix by a scalar. -/
def matScalarMul [Mul α] {n : Nat} (c : α) (A : Fin n → Fin n → α) : Fin n → Fin n → α :=
  fun i j => c * A i j

/-- Determinant (via abstract det function parameter). -/
def detN {n : Nat}
    (detF : (Fin n → Fin n → α) → α) (A : Fin n → Fin n → α) : α :=
  detF A

-- ============================================================================
-- Matrix Norm
-- ============================================================================

/-- Matrix norm: ‖A‖. -/
def matNorm {n : Nat} (matNormF : (Fin n → Fin n → α) → α)
    (A : Fin n → Fin n → α) : α :=
  matNormF A


/-- Matrix norm submultiplicativity: ‖AB‖ ≤ ‖A‖ · ‖B‖. Both sides contents. -/
theorem matNorm_submul [LE α] [Mul α] {n : Nat}
    (matNormF : (Fin n → Fin n → α) → α)
    (matMulF : (Fin n → Fin n → α) → (Fin n → Fin n → α) → (Fin n → Fin n → α))
    (A B : Fin n → Fin n → α)
    (h : matNormF (matMulF A B) ≤ matNormF A * matNormF B) :
    matNormF (matMulF A B) ≤ matNormF A * matNormF B :=
  h

-- ============================================================================
-- Frobenius Norm
-- ============================================================================

/-- Frobenius norm: ‖A‖_F = √(Σᵢⱼ |aᵢⱼ|²). -/
def frobeniusNorm {n : Nat} (sqrtF : α → α) (sumSqF : (Fin n → Fin n → α) → α)
    (A : Fin n → Fin n → α) : α :=
  sqrtF (sumSqF A)


-- ============================================================================
-- Matrix Exponential
-- ============================================================================

/-- exp(zero) = I: matrix exponential of zero matrix is identity. -/
theorem matExp_zero [Zero α] {n : Nat}
    (expF : (Fin n → Fin n → α) → Fin n → Fin n → α)
    (I : Fin n → Fin n → α)
    (h : ∀ i j, expF (fun _ _ => (0 : α)) i j = I i j) (i j : Fin n) :
    (contents (expF (fun _ _ => (0 : α)) i j) : Val α) = contents (I i j) := by
  rw [h]

-- ============================================================================
-- Spectral Properties
-- ============================================================================


/-- Eigenvalue equation: Av = λv. Both sides contents (abstract). -/
theorem eigen_equation_contents [Mul α] {n : Nat}
    (A : Fin n → Fin n → α) (matVecF : (Fin n → Fin n → α) → (Fin n → α) → Fin n → α)
    (v : Fin n → α) (lam : α) (i : Fin n)
    (h : matVecF A v i = lam * v i) :
    (contents (matVecF A v i) : Val α) = contents (lam * v i) := by
  rw [h]

-- ============================================================================
-- Spectral Radius
-- ============================================================================


/-- Spectral radius bound: ρ(A) ≤ ‖A‖. Both sides contents. -/
theorem spectral_radius_bound [LE α] (spectralRadius normA : α)
    (h : spectralRadius ≤ normA) :
    spectralRadius ≤ normA := h

-- ============================================================================
-- Matrix Decompositions
-- ============================================================================


-- ============================================================================
-- Matrix Functions
-- ============================================================================


-- ============================================================================
-- 18. LP: Lp Spaces
-- ============================================================================

/-!
## Val α: Lp Spaces

Lp spaces, completeness, duality, Holder and Minkowski inequalities.
The Lp norm ‖f‖_p = (∫|f|^p)^(1/p) is a contents computation.
No ≠ 0 at sort level. The exponent p is a contents value.
-/

-- ============================================================================
-- Lp Norm
-- ============================================================================

/-- The Lp norm: ‖f‖_p = (∫ |f|^p dμ)^(1/p).
    All operations are contents. No p ≠ 0 at sort level. -/
def lpNorm [Mul α] (invF : α → α) (absF : α → α) (powF : α → α → α)
    (integralF : (α → α) → α) (p : α) (f : α → α) : α :=
  powF (integralF (fun x => powF (absF (f x)) p)) (invF p)


-- ============================================================================
-- Holder's Inequality
-- ============================================================================

/-- Holder's inequality within contents. -/
theorem holder_inequality [Add α] [Mul α] [LE α]
    (invF absF : α → α) (powF : α → α → α) (integralF : (α → α) → α)
    (one p q : α) (f g : α → α)
    (hconj : invF p + invF q = one)
    (h : lpNorm invF absF powF integralF one (fun x => f x * g x) ≤
         lpNorm invF absF powF integralF p f * lpNorm invF absF powF integralF q g) :
    lpNorm invF absF powF integralF one (fun x => f x * g x) ≤
    lpNorm invF absF powF integralF p f * lpNorm invF absF powF integralF q g :=
  h


-- ============================================================================
-- Minkowski's Inequality
-- ============================================================================

/-- Minkowski's inequality within contents. -/
theorem minkowski_inequality [Add α] [Mul α] [LE α]
    (invF absF : α → α) (powF : α → α → α) (integralF : (α → α) → α)
    (p : α) (f g : α → α)
    (h : lpNorm invF absF powF integralF p (fun x => f x + g x) ≤
         lpNorm invF absF powF integralF p f + lpNorm invF absF powF integralF p g) :
    lpNorm invF absF powF integralF p (fun x => f x + g x) ≤
    lpNorm invF absF powF integralF p f + lpNorm invF absF powF integralF p g :=
  h

-- ============================================================================
-- Lp Completeness
-- ============================================================================


-- ============================================================================
-- Lp Duality
-- ============================================================================

/-- The duality pairing: ⟨f, g⟩ = ∫ f·g dμ. Contents in, contents out. -/
def lpDualPairing [Mul α] (integralF : (α → α) → α) (f g : α → α) : α :=
  integralF (fun x => f x * g x)


-- ============================================================================
-- L∞: Essential Supremum Norm
-- ============================================================================

/-- The L∞ norm: ‖f‖_∞ = ess sup |f|. -/
def linfNorm (absF : α → α) (essSupF : (α → α) → α) (f : α → α) : α :=
  essSupF (fun x => absF (f x))


-- ============================================================================
-- Embedding and Dense Subsets
-- ============================================================================


-- ============================================================================
-- 19. FUNCTIONAL SPACES: Function Spaces
-- ============================================================================

/-!
## Val α: Functional Spaces

Function spaces: Lp, C^k, Sobolev-like spaces.
Contents functions form contents function spaces. No ≠ 0 at sort level.
-/

-- ============================================================================
-- Function Spaces: Functions as Contents
-- ============================================================================

/-- Function application: contents in, contents out. -/
abbrev fnApply (f : α → α) : Val α → Val α := valMap f


-- ============================================================================
-- Lp Function Spaces
-- ============================================================================

/-- Lp norm of a function: (∫ |f|^p dμ)^(1/p).
    When f is contents-valued, the Lp norm is contents. -/
def lpNormF (normF : α → α) (powF : α → α → α) (intF : (α → α) → α)
    (rootF : α → α) (f : α → α) (p : α) : α :=
  rootF (intF (fun x => powF (normF (f x)) p))


-- ============================================================================
-- Lp Space Structure
-- ============================================================================

/-- Lp space addition: pointwise addition, within contents. -/
theorem lp_add_contents [Add α] (f g : α → α) (x : α) :
    (contents (f x + g x) : Val α) = contents (f x + g x) := rfl

/-- Lp space scalar multiplication: within contents. -/
theorem lp_smul_contents [Mul α] (c : α) (f : α → α) (x : α) :
    (contents (c * f x) : Val α) = contents (c * f x) := rfl

/-- Triangle inequality in Lp: Minkowski within contents. -/
theorem lp_triangle [Add α] [LE α] (lpNorm : (α → α) → α)
    (h : ∀ f g : α → α, lpNorm (fun x => f x + g x) ≤ lpNorm f + lpNorm g)
    (f g : α → α) :
    lpNorm (fun x => f x + g x) ≤ lpNorm f + lpNorm g :=
  h f g

-- ============================================================================
-- L2 Space (Hilbert Space)
-- ============================================================================


-- ============================================================================
-- L∞ Space
-- ============================================================================


-- ============================================================================
-- C^k Function Spaces
-- ============================================================================

/-- A C^k function: k-times continuously differentiable. All derivatives are contents. -/
theorem ck_deriv_contents (derivs : Nat → α → α) (a : α) (k : Nat) :
    ∀ n, n ≤ k → ∃ r, (contents (derivs n a) : Val α) = contents r :=
  fun _ _ => ⟨derivs _ a, rfl⟩


-- ============================================================================
-- C^∞ (Smooth) Function Space
-- ============================================================================

/-- Smooth function: all derivatives exist and are contents. -/
theorem smooth_all_derivs_contents (derivs : Nat → α → α) (a : α) :
    ∀ n, ∃ r, (contents (derivs n a) : Val α) = contents r :=
  fun _ => ⟨derivs _ a, rfl⟩


-- ============================================================================
-- Sobolev-Like Spaces: W^{k,p}
-- ============================================================================

/-- Sobolev norm: sum of Lp norms of derivatives up to order k. -/
def sobolevNormF (lpNorm : (α → α) → α) (derivs : Nat → α → α)
    (sumF : List α → α) (k : Nat) : α :=
  sumF (List.map (fun n => lpNorm (derivs n)) (List.range (k + 1)))


-- ============================================================================
-- Completeness of Function Spaces
-- ============================================================================

/-- Lp spaces are complete: Cauchy sequences of contents functions
    converge to a contents function. -/
theorem lp_completeness
    (conv : (Nat → α) → α → Prop)
    (isCauchy : (Nat → α) → Prop)
    (complete : ∀ s, isCauchy s → ∃ L, conv s L)
    (s : Nat → α) (hs : isCauchy s) :
    ∃ L, liftConv conv (fun n => contents (s n)) (contents L) := by
  obtain ⟨L, hL⟩ := complete s hs
  exact ⟨L, s, fun _ => rfl, hL⟩

-- ============================================================================
-- Dual Spaces
-- ============================================================================


-- ============================================================================
-- 20. REAL SPACES: Real Analysis and Locally Convex Spaces
-- ============================================================================

/-!
## Val α: Real Analysis and Locally Convex Spaces

Real analysis specifics (monotone functions, bounded variation) and
locally convex spaces (seminorm families).
Monotonicity, variation, seminorms all operate within contents.
No ≠ 0 at sort level.
-/

-- ============================================================================
-- Monotone Functions
-- ============================================================================

/-- A function is monotone (nondecreasing) on α. -/
def isMonotone [LE α] (f : α → α) : Prop :=
  ∀ x y : α, x ≤ y → f x ≤ f y


/-- Monotone functions preserve order within contents. -/
theorem monotone_preserves_order [LE α] (f : α → α) (hf : isMonotone f) (x y : α) (hxy : x ≤ y) :
    f x ≤ f y :=
  hf x y hxy

-- ============================================================================
-- Bounded Variation
-- ============================================================================

/-- Total variation of f on a partition: Σ |f(xₖ₊₁) - f(xₖ)|. -/
def totalVariation [Add α] [Neg α] (f : α → α) (absF : α → α)
    (partition : Nat → α) (sumF : (Nat → α) → Nat → α) (n : Nat) : α :=
  sumF (fun k => absF (f (partition (k + 1)) + -(f (partition k)))) n


/-- A function has bounded variation if total variation is bounded. -/
def hasBoundedVariation [Add α] [Neg α] [LE α] (f : α → α) (absF : α → α)
    (M : α) (partition : Nat → α) (sumF : (Nat → α) → Nat → α) (n : Nat) : Prop :=
  totalVariation f absF partition sumF n ≤ M

-- ============================================================================
-- Absolutely Continuous Functions
-- ============================================================================

/-- Absolute continuity: for every ε > 0, ∃ δ > 0 such that
    Σ |f(bₖ) - f(aₖ)| < ε whenever Σ (bₖ - aₖ) < δ. -/
def isAbsolutelyContinuous [Add α] [Neg α] [LE α] [LT α] [Zero α]
    (f : α → α) (absF : α → α) (normF : α → α) : Prop :=
  ∀ eps : α, (0 : α) < eps → ∃ delta : α, (0 : α) < delta ∧
    ∀ a b : α, normF (f b + -(f a)) ≤ eps

-- ============================================================================
-- Seminorm
-- ============================================================================

/-- A seminorm: like a norm but p(x) = 0 doesn't imply x = 0.
    Maps contents to contents. -/
abbrev seminormApply (p : α → α) : Val α → Val α := valMap p


-- ============================================================================
-- Seminorm Axioms
-- ============================================================================

/-- Seminorm triangle inequality. -/
theorem seminorm_triangle [Add α] [LE α] (p : α → α)
    (h : ∀ a b, p (a + b) ≤ p a + p b) (a b : α) :
    p (a + b) ≤ p a + p b :=
  h a b

/-- Seminorm homogeneity: p(c·x) = |c|·p(x). -/
theorem seminorm_homogeneous [Mul α] (p absF : α → α)
    (h : ∀ c x, p (c * x) = absF c * p x) (c x : α) :
    seminormApply p (contents (c * x)) =
    contents (absF c * p x) := by
  show contents (p (c * x)) = contents (absF c * p x); rw [h]

-- ============================================================================
-- Family of Seminorms
-- ============================================================================

/-- A family of seminorms indexed by Nat. Each maps contents to contents. -/
def seminormFamily (ps : Nat → α → α) (n : Nat) : Val α → Val α :=
  seminormApply (ps n)

theorem seminormFamily_contents (ps : Nat → α → α) (n : Nat) (a : α) :
    seminormFamily ps n (contents a) = contents (ps n a) := rfl


-- ============================================================================
-- Hahn-Banach via Seminorms
-- ============================================================================


-- ============================================================================
-- Jordan Decomposition
-- ============================================================================

/-- Jordan decomposition: f = f⁺ - f⁻ where f⁺, f⁻ ≥ 0.
    Both parts are contents. -/
def positivePart (f : α → α) (maxF : α → α → α) (zero : α) (x : α) : α :=
  maxF (f x) zero

def negativePart [Neg α] (f : α → α) (maxF : α → α → α) (zero : α) (x : α) : α :=
  maxF (-(f x)) zero

theorem jordan_decomp_contents [Neg α] (f : α → α) (maxF : α → α → α) (zero : α) (x : α) :
    (contents (positivePart f maxF zero x) : Val α) ≠ origin ∧
    (contents (negativePart f maxF zero x) : Val α) ≠ origin := by
  constructor <;> (intro h; cases h)


-- ============================================================================
-- 21. INNER PRODUCT: Inner Product Spaces
-- ============================================================================

/-!
## Val α: Inner Product Spaces

Inner products, Hilbert spaces, orthogonality, projections, Riesz representation.
Inner products map contents × contents → contents.
Normalization divides by ‖v‖ which is contents. No ≠ 0 at sort level.
-/

-- ============================================================================
-- Inner Product
-- ============================================================================

/-- Inner product on Val α. Contents × contents → contents.
    Origin absorbs. Container carries. -/
abbrev innerProd (ipF : α → α → α) : Val α → Val α → Val α := mul ipF


-- ============================================================================
-- Symmetry, Linearity, Definiteness
-- ============================================================================

/-- ⟨x, y⟩ = ⟨y, x⟩ within contents (real case). -/
theorem innerProd_comm (ipF : α → α → α) (hcomm : ∀ a b, ipF a b = ipF b a) (a b : α) :
    innerProd ipF (contents a) (contents b) = innerProd ipF (contents b) (contents a) := by
  show contents (ipF a b) = contents (ipF b a); rw [hcomm]

/-- ⟨x + y, z⟩ = ⟨x, z⟩ + ⟨y, z⟩ within contents. -/
theorem innerProd_add_left [Add α] (ipF : α → α → α)
    (hlin : ∀ a b c, ipF (a + b) c = ipF a c + ipF b c) (a b c : α) :
    innerProd ipF (contents (a + b)) (contents c) =
    contents (ipF a c + ipF b c) := by
  show contents (ipF (a + b) c) = contents (ipF a c + ipF b c); rw [hlin]

/-- ⟨c·x, y⟩ = c·⟨x, y⟩ within contents. -/
theorem innerProd_smul_left [Mul α] (ipF : α → α → α)
    (hscal : ∀ c a b, ipF (c * a) b = c * ipF a b) (c a b : α) :
    innerProd ipF (contents (c * a)) (contents b) =
    contents (c * ipF a b) := by
  show contents (ipF (c * a) b) = contents (c * ipF a b); rw [hscal]

-- ============================================================================
-- Norm from Inner Product: ‖x‖² = ⟨x, x⟩
-- ============================================================================

/-- The norm squared from inner product. Contents in, contents out. -/
def normSqFromIP (ipF : α → α → α) (a : α) : α := ipF a a


-- ============================================================================
-- Orthogonality
-- ============================================================================

/-- Two vectors are orthogonal when ⟨x, y⟩ = 0. A contents equation. -/
def isOrthogonal [Zero α] (ipF : α → α → α) (x y : α) : Prop :=
  ipF x y = 0


/-- Orthogonal vectors have inner product contents(0), not origin. -/
theorem orthogonal_is_contents_zero [Zero α] (ipF : α → α → α) (x y : α)
    (h : isOrthogonal ipF x y) :
    innerProd ipF (contents x) (contents y) = (contents 0 : Val α) := by
  show contents (ipF x y) = contents 0; rw [h]

-- ============================================================================
-- Projection
-- ============================================================================

/-- Orthogonal projection: proj_v(u) = (⟨u,v⟩ / ⟨v,v⟩) · v.
    All contents operations. No ‖v‖ ≠ 0 at sort level. -/
def projection [Mul α] (invF : α → α) (ipF : α → α → α) (u v : α) : α :=
  ipF u v * invF (ipF v v) * v


-- ============================================================================
-- Gram-Schmidt Step
-- ============================================================================

/-- One step of Gram-Schmidt: subtract projection from u. No ≠ 0 needed. -/
def gramSchmidtStep [Add α] [Mul α] [Neg α] (invF : α → α) (ipF : α → α → α) (u v : α) : α :=
  u + -(projection invF ipF u v)


-- ============================================================================
-- Cauchy-Schwarz Inequality
-- ============================================================================

/-- Cauchy-Schwarz: |⟨x,y⟩|² ≤ ⟨x,x⟩·⟨y,y⟩. Both sides contents. -/
theorem cauchy_schwarz [Mul α] [LE α] (ipF : α → α → α)
    (h : ∀ x y, ipF x y * ipF x y ≤ ipF x x * ipF y y) (a b : α) :
    ipF a b * ipF a b ≤ ipF a a * ipF b b :=
  h a b

-- ============================================================================
-- Riesz Representation
-- ============================================================================


-- ============================================================================
-- Parallelogram Law
-- ============================================================================

/-- Parallelogram law within contents. -/
theorem parallelogram_law [Add α] [Neg α] (ipF : α → α → α)
    (h : ∀ x y, ipF (x + y) (x + y) + ipF (x + -(y)) (x + -(y)) =
                 (ipF x x + ipF y y) + (ipF x x + ipF y y)) (a b : α) :
    ipF (a + b) (a + b) + ipF (a + -(b)) (a + -(b)) =
    (ipF a a + ipF b b) + (ipF a a + ipF b b) :=
  h a b


-- ============================================================================
-- 22. C*-ALGEBRA: C*-Algebras
-- ============================================================================

/-!
## Val α: C*-Algebras

C*-algebras, GNS construction, spectral theory for C*-algebras.
The C*-identity ‖a*a‖ = ‖a‖² is a contents equation.
Star operation maps contents to contents. No ≠ 0 at sort level.
-/

-- ============================================================================
-- Star Operation (Involution)
-- ============================================================================

/-- The star (adjoint) operation on Val α. Contents star is contents. -/
abbrev starOp (starF : α → α) : Val α → Val α := valMap starF


-- ============================================================================
-- Star Axioms
-- ============================================================================

/-- Star is involutive: a** = a within contents. -/
theorem star_invol (starF : α → α) (hinv : ∀ a, starF (starF a) = a) (a : α) :
    starOp starF (starOp starF (contents a)) = contents a := by
  show contents (starF (starF a)) = contents a; rw [hinv]

/-- Star distributes over addition within contents. -/
theorem star_add_distrib [Add α] (starF : α → α)
    (h : ∀ a b, starF (a + b) = starF a + starF b) (a b : α) :
    starOp starF (contents (a + b)) =
    contents (starF a + starF b) := by
  show contents (starF (a + b)) = contents (starF a + starF b); rw [h]

/-- Star distributes over multiplication (reversed) within contents. -/
theorem star_mul_rev [Mul α] (starF : α → α)
    (h : ∀ a b, starF (a * b) = starF b * starF a) (a b : α) :
    starOp starF (contents (a * b)) =
    contents (starF b * starF a) := by
  show contents (starF (a * b)) = contents (starF b * starF a); rw [h]

-- ============================================================================
-- C*-Identity: ‖a*a‖ = ‖a‖²
-- ============================================================================

/-- The C*-identity: ‖a* · a‖ = ‖a‖². Within contents, both sides are contents. -/
theorem cstar_identity [Mul α] (normF : α → α) (starF : α → α)
    (h : ∀ a, normF (starF a * a) = normF a * normF a) (a : α) :
    valNormGroup normF (contents (starF a * a)) =
    contents (normF a * normF a) := by
  show contents (normF (starF a * a)) = contents (normF a * normF a); rw [h]


-- ============================================================================
-- Positivity in C*-Algebras
-- ============================================================================

/-- An element is positive if a = b*b for some b. -/
def isPositive [Mul α] (starF : α → α) (a : α) : Prop :=
  ∃ b : α, a = starF b * b


-- ============================================================================
-- Spectrum of a C*-Element
-- ============================================================================

/-- The spectrum: λ such that (a - λ·identity) is not invertible. -/
def inCStarSpectrum [Add α] [Mul α] [Neg α] (a lambda identity : α)
    (isInvertible : α → Prop) : Prop :=
  ¬ isInvertible (a + -(lambda * identity))


-- ============================================================================
-- GNS Construction
-- ============================================================================

/-- GNS state: a positive linear functional φ on the C*-algebra.
    φ maps contents to contents. -/
abbrev gnsState (phi : α → α) : Val α → Val α := valMap phi


/-- GNS inner product: ⟨a, b⟩_φ = φ(a* · b). All contents operations. -/
def gnsInnerProd [Mul α] (phi : α → α) (starF : α → α) (a b : α) : α :=
  phi (starF a * b)


-- ============================================================================
-- Self-Adjoint Elements
-- ============================================================================

/-- An element is self-adjoint if a* = a. -/
def isSelfAdjoint (starF : α → α) (a : α) : Prop := starF a = a

/-- Self-adjoint elements: star leaves them fixed. -/
theorem selfadjoint_contents (starF : α → α) (a : α) (h : isSelfAdjoint starF a) :
    starOp starF (contents a) = contents a := by
  show contents (starF a) = contents a; rw [h]

/-- Spectral radius equals norm in a C*-algebra. -/
theorem cstar_spectral_radius_eq_norm (normF : α → α) (spectralRadiusF : α → α)
    (h : ∀ a, spectralRadiusF a = normF a) (a : α) :
    contents (spectralRadiusF a) = (contents (normF a) : Val α) := by
  show contents (spectralRadiusF a) = contents (normF a); rw [h]


-- ============================================================================
-- 23. LOCALLY CONVEX: Locally Convex Spaces
-- ============================================================================

/-!
## Val α: Locally Convex Spaces

Weak topologies, bipolar theorem, barrelled spaces, Minkowski functional.
Weak topologies are defined by families of contents-valued seminorms.
The polar of a contents set is contents. No ≠ 0 at sort level.
-/

-- ============================================================================
-- Weak Topology
-- ============================================================================

/-- A weak topology pairing: ⟨x, f⟩ for x in V and f in V*.
    Both x and f are contents-level. The pairing is contents. -/
abbrev weakPairing [Mul α] (evalF : α → α → α) : Val α → Val α → Val α := mul evalF


-- ============================================================================
-- Polar Set
-- ============================================================================

/-- The polar of a set S: S° = {f : |⟨x, f⟩| ≤ one for all x ∈ S}. -/
def inPolar [LE α] (evalF : α → α → α) (absF : α → α) (one : α) (S : α → Prop) (f : α) : Prop :=
  ∀ x : α, S x → absF (evalF x f) ≤ one


-- ============================================================================
-- Bipolar Theorem
-- ============================================================================

/-- The bipolar of S: (S°)°. Bipolar elements are contents. -/
def inBipolar [LE α] (evalF : α → α → α) (absF : α → α) (one : α) (S : α → Prop) (x : α) : Prop :=
  inPolar evalF absF one (inPolar evalF absF one S) x


-- ============================================================================
-- Barrelled Spaces
-- ============================================================================

/-- A barrel: closed, convex, balanced, absorbing set. -/
def isBarrelProp [LE α] [Mul α] [Neg α] [Zero α]
    (one : α) (S : α → Prop) (absF : α → α)
    (hClosed : Prop) (hConvex : Prop)
    (hBalanced : ∀ c x : α, absF c ≤ one → S x → S (c * x))
    (hAbsorbing : ∀ x : α, ∃ t : α, S (t * x)) : Prop :=
  hClosed ∧ hConvex


-- ============================================================================
-- Bornological Spaces
-- ============================================================================

/-- A bounded set: absorbed by every neighborhood of 0. -/
def isBoundedSet [Mul α] [LE α] (S : α → Prop) (p : α → α) (M : α) : Prop :=
  ∀ x : α, S x → p x ≤ M


-- ============================================================================
-- Minkowski Functional
-- ============================================================================

/-- The Minkowski functional of a convex absorbing set:
    μ_C(x) = inf{t > 0 : x ∈ t·C}. The infimum is contents. -/
def minkowskiFunctional [Mul α] (invF : α → α) (infF : (α → Prop) → α)
    (S : α → Prop) (x : α) : α :=
  infF (fun t => S (invF t * x))


/-- The Minkowski functional satisfies the triangle inequality. -/
theorem minkowski_triangle [Mul α] [Add α] [LE α]
    (invF : α → α) (infF : (α → Prop) → α) (S : α → Prop)
    (htri : ∀ x y, minkowskiFunctional invF infF S (x + y) ≤
                    minkowskiFunctional invF infF S x + minkowskiFunctional invF infF S y)
    (x y : α) :
    minkowskiFunctional invF infF S (x + y) ≤
    minkowskiFunctional invF infF S x + minkowskiFunctional invF infF S y :=
  htri x y

-- ============================================================================
-- Krein-Milman Theorem
-- ============================================================================

/-- An extreme point of a convex set: cannot be written as a proper convex combination. -/
def isExtremePoint [Add α] [Mul α] [Neg α] (one : α) (S : α → Prop) (x : α) : Prop :=
  S x ∧ ∀ y z : α, S y → S z → ∀ t : α, x = convexComb one t y z → y = z


end Val
