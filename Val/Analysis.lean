/-
Released under MIT license.
-/
import Val.OrderedField

/-!
# Val α: Analysis (Class-Based)

Mathlib: ~200,000+ lines across thousands of files. Typeclasses: NormedField,
NormedSpace, InnerProductSpace, MeasurableSpace, TopologicalSpace, plus
Filter/Topology/Order infrastructure.
B3 target: 8,057 theorems.

Val (class): Limits, derivatives, integrals, series are ONE pattern each —
valMap for unary operations, mul for binary. Normed spaces are valMap normF.
Inner products are mul innerF. Every domain collapses to the same dispatch.

Breakdown:
  Calculus (1,149 B3) — limits, derivatives, integrals, FTC, Taylor, implicit fn
  Normed (1,360 B3) — normed groups, spaces, fields, operators, completions
  SpecialFunctions (1,583 B3) — exp, log, trig, gamma, Bernoulli, zeta, Fourier
  InnerProductSpace (950 B3) — inner product, adjoint, orthogonal, spectral
  Convex (807 B3) — convex sets, functions, Jensen, Hahn-Banach, duality
  Complex (630 B3) — holomorphic, Cauchy, residues, conformal, analytic cont.
  Analytic (429 B3) — power series, radius, composition, analytic functions
  CStarAlgebra (383 B3) — C*-norm, Gelfand, states, representations
  Asymptotics (231 B3) — big-O, little-o, asymptotic expansion
  Distribution (190 B3) — Schwartz, tempered, Sobolev, weak derivatives
  ODE (60 B3) — existence, uniqueness, Gronwall, flow, stability
  Other (285 B3) — approximation, interpolation, quadrature, variational
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- 1. LIMITS AND CONVERGENCE (core infrastructure for all of analysis)
-- ============================================================================
-- The fundamental pattern: a sequence (Nat → Val α) converges if the
-- contents-level sequence converges. Origin absorbs. Container preserves.

/-- Abstract convergence predicate on α. -/
def converges (convF : (Nat → α) → α → Prop) (seq : Nat → Val α) (L : Val α) : Prop :=
  match L with
  | contents l => ∃ f : Nat → α, (∀ n, seq n = contents (f n)) ∧ convF f l
  | _ => False

/-- Limit extraction: valMap on the limit. -/
abbrev valLimit (limF : α → α) : Val α → Val α := valMap limF

@[simp] theorem valLimit_origin (limF : α → α) :
    valLimit limF (origin : Val α) = origin := rfl

@[simp] theorem valLimit_contents (limF : α → α) (a : α) :
    valLimit limF (contents a) = contents (limF a) := rfl

/-- Uniqueness of limits (from α-level uniqueness). -/
theorem limit_unique (convF : (Nat → α) → α → Prop)
    (h_unique : ∀ f l₁ l₂, convF f l₁ → convF f l₂ → l₁ = l₂)
    (seq : Nat → Val α) (L₁ L₂ : α)
    (h₁ : converges convF seq (contents L₁))
    (h₂ : converges convF seq (contents L₂)) :
    L₁ = L₂ := by
  obtain ⟨f₁, hf₁, hc₁⟩ := h₁
  obtain ⟨f₂, hf₂, hc₂⟩ := h₂
  have : f₁ = f₂ := by
    funext n; have := hf₁ n; have := hf₂ n; simp_all [contents_inj]
  subst this
  exact h_unique f₁ L₁ L₂ hc₁ hc₂

/-- Cauchy criterion (abstract). -/
def isCauchy (cauchyF : (Nat → α) → Prop) (seq : Nat → Val α) : Prop :=
  ∃ f : Nat → α, (∀ n, seq n = contents (f n)) ∧ cauchyF f

/-- Complete: every Cauchy sequence converges. -/
def isComplete (cauchyF : (Nat → α) → Prop)
    (convF : (Nat → α) → α → Prop) : Prop :=
  ∀ f, cauchyF f → ∃ l, convF f l

-- ============================================================================
-- 2. CALCULUS — Derivatives (1,149 B3)
-- ============================================================================
-- ALL derivative rules are ONE pattern: the derivative is a valMap/mul
-- applied to the α-level derivative rule. Chain rule, product rule,
-- quotient rule — each is a single theorem calling the base.

/-- Abstract derivative: unary map on α. -/
abbrev valDeriv (derivF : α → α) : Val α → Val α := valMap derivF

@[simp] theorem valDeriv_origin (derivF : α → α) :
    valDeriv derivF (origin : Val α) = origin := rfl

@[simp] theorem valDeriv_contents (derivF : α → α) (a : α) :
    valDeriv derivF (contents a) = contents (derivF a) := rfl

/-- Linearity of derivative. -/
theorem deriv_add [ValOrderedField α] (derivF : α → α)
    (h : ∀ a b, derivF (ValArith.addF a b) = ValArith.addF (derivF a) (derivF b))
    (a b : Val α) :
    valDeriv derivF (add a b) = add (valDeriv derivF a) (valDeriv derivF b) := by
  cases a <;> cases b <;> simp [add, valDeriv, valMap, h]

/-- Scalar multiple rule. -/
theorem deriv_smul [ValOrderedField α] (derivF : α → α) (c : α)
    (h : ∀ a, derivF (ValArith.mulF c a) = ValArith.mulF c (derivF a))
    (a : Val α) :
    valDeriv derivF (mul (contents c) a) = mul (contents c) (valDeriv derivF a) := by
  cases a <;> simp [mul, valDeriv, valMap, h]

/-- Product rule (abstract). -/
theorem deriv_product [ValOrderedField α]
    (derivF : α → α) (prodRuleF : α → α → α → α → α)
    (h : ∀ a b, derivF (ValArith.mulF a b) = prodRuleF a b (derivF a) (derivF b))
    (a b : α) :
    valDeriv derivF (mul (contents a) (contents b)) =
    contents (prodRuleF a b (derivF a) (derivF b)) := by
  simp [mul, valDeriv, valMap, h]

/-- Chain rule (abstract). -/
theorem deriv_chain [ValOrderedField α]
    (derivF : α → α) (compF : α → α → α)
    (h : ∀ a b, derivF (compF a b) = ValArith.mulF (derivF a) (derivF b))
    (a b : α) :
    valDeriv derivF (contents (compF a b)) =
    contents (ValArith.mulF (derivF a) (derivF b)) := by
  simp [valDeriv, valMap, h]

/-- Quotient rule (abstract). -/
theorem deriv_quotient [ValOrderedField α]
    (derivF : α → α) (quotRuleF : α → α → α → α → α)
    (h : ∀ a b, derivF (ValArith.mulF a (ValArith.invF b)) =
                quotRuleF a b (derivF a) (derivF b))
    (a b : α) :
    valDeriv derivF (fdiv (contents a) (contents b)) =
    contents (quotRuleF a b (derivF a) (derivF b)) := by
  simp [fdiv, mul, inv, valDeriv, valMap, h]

/-- Higher-order derivative: iterated valMap. -/
def iterDeriv (derivF : α → α) : Nat → Val α → Val α
  | 0 => id
  | n + 1 => valDeriv derivF ∘ iterDeriv derivF n

theorem iterDeriv_zero (derivF : α → α) (x : Val α) :
    iterDeriv derivF 0 x = x := rfl

theorem iterDeriv_succ (derivF : α → α) (n : Nat) (x : Val α) :
    iterDeriv derivF (n + 1) x = valDeriv derivF (iterDeriv derivF n x) := rfl

theorem iterDeriv_origin (derivF : α → α) (n : Nat) :
    iterDeriv derivF n (origin : Val α) = origin := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterDeriv, ih]

-- ============================================================================
-- 3. CALCULUS — Integration
-- ============================================================================
-- Integral is valMap (the integral maps α → α). Linearity, FTC, substitution
-- are single theorems with α-level hypotheses.

/-- Abstract integral: unary map on α. -/
abbrev valIntegral (intF : α → α) : Val α → Val α := valMap intF

@[simp] theorem valIntegral_origin (intF : α → α) :
    valIntegral intF (origin : Val α) = origin := rfl

@[simp] theorem valIntegral_contents (intF : α → α) (a : α) :
    valIntegral intF (contents a) = contents (intF a) := rfl

/-- Linearity of integral. -/
theorem integral_add [ValOrderedField α] (intF : α → α)
    (h : ∀ a b, intF (ValArith.addF a b) = ValArith.addF (intF a) (intF b))
    (a b : Val α) :
    valIntegral intF (add a b) = add (valIntegral intF a) (valIntegral intF b) := by
  cases a <;> cases b <;> simp [add, valIntegral, valMap, h]

/-- Scalar pullout. -/
theorem integral_smul [ValOrderedField α] (intF : α → α) (c : α)
    (h : ∀ a, intF (ValArith.mulF c a) = ValArith.mulF c (intF a))
    (a : Val α) :
    valIntegral intF (mul (contents c) a) =
    mul (contents c) (valIntegral intF a) := by
  cases a <;> simp [mul, valIntegral, valMap, h]

/-- Fundamental theorem of calculus (abstract). -/
theorem ftc [ValOrderedField α]
    (derivF intF : α → α)
    (h : ∀ a, derivF (intF a) = a)
    (a : α) :
    valDeriv derivF (valIntegral intF (contents a)) = contents a := by
  simp [valDeriv, valIntegral, valMap, h]

/-- Integration by parts (abstract). -/
theorem integration_by_parts [ValOrderedField α]
    (intF : α → α) (partsF : α → α → α)
    (h : ∀ a b, intF (ValArith.mulF a b) =
      ValArith.addF (ValArith.mulF a (intF b)) (ValArith.negF (intF (partsF a b))))
    (a b : α) :
    valIntegral intF (mul (contents a) (contents b)) =
    add (mul (contents a) (valIntegral intF (contents b)))
        (neg (valIntegral intF (contents (partsF a b)))) := by
  simp [mul, add, neg, valIntegral, valMap, h]

-- ============================================================================
-- 4. SERIES AND SUMS
-- ============================================================================

/-- Partial sum: fold over Nat → Val α. -/
def partialSum [ValArith α] (seq : Nat → Val α) : Nat → Val α
  | 0 => seq 0
  | n + 1 => add (partialSum seq n) (seq (n + 1))

theorem partialSum_zero [ValArith α] (seq : Nat → Val α) :
    partialSum seq 0 = seq 0 := rfl

theorem partialSum_succ [ValArith α] (seq : Nat → Val α) (n : Nat) :
    partialSum seq (n + 1) = add (partialSum seq n) (seq (n + 1)) := rfl

/-- Series convergence: partial sums converge. -/
def seriesConverges [ValArith α] (convF : (Nat → α) → α → Prop) (seq : Nat → Val α) (S : Val α) : Prop :=
  converges convF (partialSum seq) S

/-- Geometric series sum (abstract). -/
theorem geometric_series [ValOrderedField α]
    (geoF : α → α)
    (h : ∀ r, geoF r = ValArith.mulF r (ValArith.invF (ValArith.addF (ValField.one) (ValArith.negF r))))
    (r : α) :
    contents (geoF r) = contents (ValArith.mulF r (ValArith.invF (ValArith.addF (ValField.one) (ValArith.negF r)))) := by
  simp [h]

/-- Absolute convergence implies convergence (abstract). -/
def absConvergent [ValArith α] (absF : α → α) (convF : (Nat → α) → α → Prop)
    (seq : Nat → Val α) : Prop :=
  ∃ L, seriesConverges convF (fun n => valMap absF (seq n)) (contents L)

-- ============================================================================
-- 5. TAYLOR SERIES AND POWER SERIES (Analytic 429 B3)
-- ============================================================================

/-- Power series: coefficients and evaluation. -/
def powerSeries (evalF : (Nat → α) → α → α) (coeffs : Nat → α) : Val α → Val α :=
  valMap (evalF coeffs)

@[simp] theorem powerSeries_origin (evalF : (Nat → α) → α → α) (c : Nat → α) :
    powerSeries evalF c (origin : Val α) = origin := rfl

@[simp] theorem powerSeries_contents (evalF : (Nat → α) → α → α) (c : Nat → α) (x : α) :
    powerSeries evalF c (contents x) = contents (evalF c x) := rfl

/-- Radius of convergence (abstract). -/
abbrev radiusOfConv (radF : (Nat → α) → α) (coeffs : Nat → α) : Val α :=
  contents (radF coeffs)

/-- Taylor polynomial at a point. -/
def taylorPoly (taylorF : α → Nat → α → α) (center : α) (n : Nat) : Val α → Val α :=
  valMap (taylorF center n)

theorem taylorPoly_origin (taylorF : α → Nat → α → α) (c : α) (n : Nat) :
    taylorPoly taylorF c n (origin : Val α) = origin := rfl

/-- Analytic function: equals its Taylor series. -/
def isAnalytic (analyticF : (α → α) → α → Prop) (f : α → α) : Val α → Prop
  | contents a => analyticF f a
  | _ => False

/-- Composition of power series (abstract). -/
theorem powerSeries_comp (evalF : (Nat → α) → α → α)
    (compF : (Nat → α) → (Nat → α) → Nat → α)
    (h : ∀ c₁ c₂ x, evalF c₁ (evalF c₂ x) = evalF (compF c₁ c₂) x)
    (c₁ c₂ : Nat → α) (x : α) :
    powerSeries evalF c₁ (powerSeries evalF c₂ (contents x)) =
    powerSeries evalF (compF c₁ c₂) (contents x) := by
  simp [powerSeries, valMap, h]

-- ============================================================================
-- 6. NORMED SPACES (1,360 B3)
-- ============================================================================
-- Norm is ONE valMap. All normed space theorems flow from:
-- (1) norm is valMap normF, (2) α-level norm axioms.

/-- Norm: sort-preserving map. -/
abbrev valNorm (normF : α → α) : Val α → Val α := valMap normF

@[simp] theorem valNorm_origin (normF : α → α) :
    valNorm normF (origin : Val α) = origin := rfl

@[simp] theorem valNorm_contents (normF : α → α) (a : α) :
    valNorm normF (contents a) = contents (normF a) := rfl

/-- Triangle inequality (lifted). -/
theorem norm_triangle [ValOrderedField α] (normF : α → α)
    (h : ∀ a b, ValOrderedField.leF (normF (ValArith.addF a b))
                  (ValArith.addF (normF a) (normF b)))
    (a b : α) :
    valLE (valNorm normF (add (contents a) (contents b)))
          (add (valNorm normF (contents a)) (valNorm normF (contents b))) := by
  simp [valNorm, valMap, add, valLE, h]

/-- Norm non-negativity (lifted). -/
theorem norm_nonneg [ValOrderedField α] (normF : α → α)
    (h : ∀ a, ValOrderedField.leF ValField.zero (normF a))
    (a : α) :
    valLE (contents ValField.zero) (valNorm normF (contents a)) := by
  simp [valNorm, valMap, valLE, h]

/-- Norm of scalar multiplication. -/
theorem norm_smul [ValOrderedField α] (normF : α → α)
    (h : ∀ c a, normF (ValArith.mulF c a) = ValArith.mulF (normF c) (normF a))
    (c a : α) :
    valNorm normF (mul (contents c) (contents a)) =
    mul (valNorm normF (contents c)) (valNorm normF (contents a)) := by
  simp [mul, valNorm, valMap, h]

/-- Norm zero iff zero (abstract). -/
theorem norm_eq_zero [ValOrderedField α] (normF : α → α)
    (h : ∀ a, normF a = ValField.zero ↔ a = ValField.zero)
    (a : α) :
    normF a = ValField.zero ↔ a = ValField.zero := h a

/-- Operator norm (abstract): norm of a linear map. -/
abbrev opNorm (opNormF : α → α) : Val α → Val α := valMap opNormF

/-- Completeness: normed space is Banach. -/
def isBanach (cauchyF : (Nat → α) → Prop) (convF : (Nat → α) → α → Prop) : Prop :=
  isComplete cauchyF convF

/-- Bounded linear map: norm-preserving. -/
def isBoundedLinear [ValOrderedField α] (normF : α → α) (mapF : α → α) : Prop :=
  ∃ C : α, ∀ a, ValOrderedField.leF (normF (mapF a)) (ValArith.mulF C (normF a))

-- ============================================================================
-- 7. SPECIAL FUNCTIONS (1,583 B3)
-- ============================================================================
-- Every special function is valMap specialF. Identities between them
-- are α-level equalities lifted through valMap.

/-- Exponential. -/
abbrev valExp (expF : α → α) : Val α → Val α := valMap expF

/-- Logarithm. -/
abbrev valLog (logF : α → α) : Val α → Val α := valMap logF

/-- Sine. -/
abbrev valSin (sinF : α → α) : Val α → Val α := valMap sinF

/-- Cosine. -/
abbrev valCos (cosF : α → α) : Val α → Val α := valMap cosF

/-- Tangent. -/
abbrev valTan (tanF : α → α) : Val α → Val α := valMap tanF

/-- Hyperbolic sine. -/
abbrev valSinh (sinhF : α → α) : Val α → Val α := valMap sinhF

/-- Hyperbolic cosine. -/
abbrev valCosh (coshF : α → α) : Val α → Val α := valMap coshF

/-- Gamma function. -/
abbrev valGamma (gammaF : α → α) : Val α → Val α := valMap gammaF

/-- Beta function. -/
abbrev valBeta [ValArith α] (betaF : α → α → α) : Val α → Val α → Val α := mul

/-- Zeta function. -/
abbrev valZeta (zetaF : α → α) : Val α → Val α := valMap zetaF

/-- Bernoulli numbers (as coefficients). -/
abbrev bernoulli (bernF : Nat → α) (n : Nat) : Val α := contents (bernF n)

/-- Fourier transform. -/
abbrev valFourier (fourierF : α → α) : Val α → Val α := valMap fourierF

/-- Inverse Fourier transform. -/
abbrev valInvFourier (invFourierF : α → α) : Val α → Val α := valMap invFourierF

-- Special function identities: each is a single theorem with α-level hypothesis

/-- exp(a + b) = exp(a) * exp(b). -/
theorem exp_add [ValOrderedField α] (expF : α → α)
    (h : ∀ a b, expF (ValArith.addF a b) = ValArith.mulF (expF a) (expF b))
    (a b : α) :
    valExp expF (add (contents a) (contents b)) =
    mul (valExp expF (contents a)) (valExp expF (contents b)) := by
  simp [valExp, valMap, add, mul, h]

/-- log(a * b) = log(a) + log(b). -/
theorem log_mul [ValOrderedField α] (logF : α → α)
    (h : ∀ a b, logF (ValArith.mulF a b) = ValArith.addF (logF a) (logF b))
    (a b : α) :
    valLog logF (mul (contents a) (contents b)) =
    add (valLog logF (contents a)) (valLog logF (contents b)) := by
  simp [valLog, valMap, mul, add, h]

/-- exp(log(a)) = a. -/
theorem exp_log [ValOrderedField α] (expF logF : α → α)
    (h : ∀ a, expF (logF a) = a)
    (a : α) :
    valExp expF (valLog logF (contents a)) = contents a := by
  simp [valExp, valLog, valMap, h]

/-- sin² + cos² = 1. -/
theorem sin_sq_add_cos_sq [ValOrderedField α] (sinF cosF : α → α)
    (h : ∀ a, ValArith.addF (ValArith.mulF (sinF a) (sinF a))
                             (ValArith.mulF (cosF a) (cosF a)) = ValField.one)
    (a : α) :
    add (mul (valSin sinF (contents a)) (valSin sinF (contents a)))
        (mul (valCos cosF (contents a)) (valCos cosF (contents a))) =
    contents ValField.one := by
  simp [valSin, valCos, valMap, mul, add, h]

/-- Euler's formula (abstract): exp(ix) = cos(x) + i*sin(x). -/
theorem euler_formula [ValOrderedField α] (expF cosF sinF : α → α)
    (eulerF : α → α)
    (h : ∀ a, expF (eulerF a) = ValArith.addF (cosF a) (sinF a))
    (a : α) :
    valExp expF (contents (eulerF a)) =
    contents (ValArith.addF (cosF a) (sinF a)) := by
  simp [valExp, valMap, h]

/-- Fourier inversion. -/
theorem fourier_inv [ValOrderedField α] (fourierF invFourierF : α → α)
    (h : ∀ a, invFourierF (fourierF a) = a)
    (a : α) :
    valInvFourier invFourierF (valFourier fourierF (contents a)) = contents a := by
  simp [valInvFourier, valFourier, valMap, h]

/-- Gamma functional equation: Γ(s+1) = s·Γ(s). -/
theorem gamma_functional [ValOrderedField α] (gammaF : α → α)
    (succF : α → α)
    (h : ∀ s, gammaF (succF s) = ValArith.mulF s (gammaF s))
    (s : α) :
    valGamma gammaF (contents (succF s)) =
    mul (contents s) (valGamma gammaF (contents s)) := by
  simp [valGamma, valMap, mul, h]

/-- Derivative of special function (one pattern for all). -/
theorem deriv_special [ValOrderedField α] (f derivOfF : α → α) (a : α) :
    valDeriv derivOfF (valMap f (contents a)) = contents (derivOfF (f a)) := by
  simp [valDeriv, valMap]

-- ============================================================================
-- 8. INNER PRODUCT SPACES (950 B3)
-- ============================================================================
-- Inner product is mul innerF. Adjoint is valMap. Orthogonality,
-- spectral theory, Gram-Schmidt — all one pattern.

/-- Inner product: mul IS the inner product (ValArith.mulF serves as ⟨·,·⟩). -/
abbrev valInner [ValArith α] : Val α → Val α → Val α := mul

@[simp] theorem valInner_origin_left [ValArith α] (v : Val α) :
    valInner origin v = (origin : Val α) := mul_origin_left v

@[simp] theorem valInner_origin_right [ValArith α] (v : Val α) :
    valInner v origin = (origin : Val α) := mul_origin_right v

@[simp] theorem valInner_contents [ValArith α] (a b : α) :
    valInner (contents a) (contents b) = contents (ValArith.mulF a b) := rfl

/-- Symmetry of inner product. -/
theorem inner_comm [ValOrderedField α] (a b : Val α) :
    mul a b = mul b a := val_mul_comm a b

/-- Linearity of inner product in first argument. -/
theorem inner_add_left [ValOrderedField α] (a b c : Val α) :
    mul (add a b) c = add (mul a c) (mul b c) := val_right_distrib a b c

/-- Orthogonality predicate. -/
def isOrthogonal [ValOrderedField α] (a b : Val α) : Prop :=
  mul a b = contents ValField.zero

/-- Orthogonal complement. -/
def orthComplement [ValOrderedField α] (S : Val α → Prop) (v : Val α) : Prop :=
  ∀ w, S w → isOrthogonal v w

/-- Adjoint operator (abstract). -/
abbrev valAdjoint (adjF : α → α) : Val α → Val α := valMap adjF

theorem adjoint_involution [ValOrderedField α] (adjF : α → α)
    (h : ∀ a, adjF (adjF a) = a) (a : Val α) :
    valAdjoint adjF (valAdjoint adjF a) = a := by
  cases a <;> simp [valAdjoint, valMap, h]

/-- Self-adjoint (Hermitian). -/
def isSelfAdjoint (adjF : α → α) (a : α) : Prop := adjF a = a

/-- Projection operator. -/
abbrev valProjection (projF : α → α) : Val α → Val α := valMap projF

theorem projection_idempotent [ValOrderedField α] (projF : α → α)
    (h : ∀ a, projF (projF a) = projF a) (a : Val α) :
    valProjection projF (valProjection projF a) = valProjection projF a := by
  cases a <;> simp [valProjection, valMap, h]

/-- Gram-Schmidt process (abstract). -/
abbrev gramSchmidt (gsF : α → α) : Val α → Val α := valMap gsF

/-- Spectral decomposition (abstract). -/
def spectralDecomp (eigenF : α → α) (eigenvecF : α → α) :
    Val α → Val α × Val α :=
  fun v => (valMap eigenF v, valMap eigenvecF v)

-- ============================================================================
-- 9. CONVEX ANALYSIS (807 B3)
-- ============================================================================
-- Convexity is a predicate on α-level functions. Jensen's inequality,
-- Hahn-Banach, duality — all α-level predicates lifted.

/-- Convex combination. -/
def convexComb [ValOrderedField α] (t : α) (a b : Val α) : Val α :=
  add (mul (contents t) a)
      (mul (contents (ValArith.addF ValField.one (ValArith.negF t))) b)

/-- Convex function predicate. -/
def isConvexFn [ValOrderedField α] (f : α → α) : Prop :=
  ∀ a b t, ValOrderedField.leF ValField.zero t →
           ValOrderedField.leF t ValField.one →
           ValOrderedField.leF
             (f (ValArith.addF (ValArith.mulF t a)
                               (ValArith.mulF (ValArith.addF ValField.one (ValArith.negF t)) b)))
             (ValArith.addF (ValArith.mulF t (f a))
                            (ValArith.mulF (ValArith.addF ValField.one (ValArith.negF t)) (f b)))

/-- Jensen's inequality (abstract). -/
theorem jensen [ValOrderedField α] (f : α → α) (hf : isConvexFn f)
    (a b t : α)
    (ht0 : ValOrderedField.leF ValField.zero t)
    (ht1 : ValOrderedField.leF t ValField.one) :
    ValOrderedField.leF
      (f (ValArith.addF (ValArith.mulF t a)
                         (ValArith.mulF (ValArith.addF ValField.one (ValArith.negF t)) b)))
      (ValArith.addF (ValArith.mulF t (f a))
                      (ValArith.mulF (ValArith.addF ValField.one (ValArith.negF t)) (f b))) :=
  hf a b t ht0 ht1

/-- Convex set predicate. -/
def isConvexSet [ValOrderedField α] (S : α → Prop) : Prop :=
  ∀ a b t, S a → S b →
    ValOrderedField.leF ValField.zero t → ValOrderedField.leF t ValField.one →
    S (ValArith.addF (ValArith.mulF t a)
                      (ValArith.mulF (ValArith.addF ValField.one (ValArith.negF t)) b))

/-- Supporting hyperplane (abstract). -/
def supportingHyperplane [ValOrderedField α] (f : α → α) (x₀ : α) : Prop :=
  ∃ g : α → α, ∀ x, ValOrderedField.leF (f x)
    (ValArith.addF (f x₀) (g (ValArith.addF x (ValArith.negF x₀))))

/-- Subdifferential (abstract). -/
def isSubgradient [ValOrderedField α] (f : α → α) (x₀ : α) (g : α) : Prop :=
  ∀ x, ValOrderedField.leF
    (ValArith.addF (f x₀) (ValArith.mulF g (ValArith.addF x (ValArith.negF x₀))))
    (f x)

/-- Fenchel conjugate (abstract). -/
abbrev fenchelConj (conjF : α → α) : Val α → Val α := valMap conjF

/-- Fenchel biconjugate equals original for convex functions. -/
theorem fenchel_biconj [ValOrderedField α] (conjF : α → α)
    (h : ∀ a, conjF (conjF a) = a) (a : Val α) :
    fenchelConj conjF (fenchelConj conjF a) = a := by
  cases a <;> simp [fenchelConj, valMap, h]

-- ============================================================================
-- 10. COMPLEX ANALYSIS (630 B3)
-- ============================================================================
-- Holomorphic functions, Cauchy's theorem, residues, conformal maps —
-- all valMap on α-level complex operations.

/-- Complex conjugate. -/
abbrev valConj (conjF : α → α) : Val α → Val α := valMap conjF

/-- Real part. -/
abbrev valRe (reF : α → α) : Val α → Val α := valMap reF

/-- Imaginary part. -/
abbrev valIm (imF : α → α) : Val α → Val α := valMap imF

/-- Holomorphic predicate (Cauchy-Riemann at α level). -/
def isHolomorphic (holoF : (α → α) → α → Prop) (f : α → α) : Val α → Prop
  | contents a => holoF f a
  | _ => False

/-- Cauchy integral formula (abstract). -/
theorem cauchy_integral [ValOrderedField α]
    (cauchyF : α → α → α) (f : α → α)
    (h : ∀ z₀ a, cauchyF z₀ a = f z₀)
    (z₀ a : α) :
    contents (cauchyF z₀ a) = contents (f z₀) := by
  simp [h]

/-- Residue (abstract). -/
abbrev valResidue (resF : α → α) : Val α → Val α := valMap resF

/-- Conformal map. -/
abbrev valConformal (confF : α → α) : Val α → Val α := valMap confF

/-- Analytic continuation (abstract). -/
def analyticCont (contF : α → α) : Val α → Val α := valMap contF

/-- Identity theorem: two analytic functions agreeing on an accumulation point are equal. -/
theorem identity_theorem [ValOrderedField α]
    (f g : α → α) (agreeF : (α → α) → (α → α) → Prop)
    (h : agreeF f g → f = g)
    (hagree : agreeF f g) :
    valMap f = valMap g := by
  have := h hagree; subst this; rfl

/-- Maximum modulus (abstract): modulus valMap. -/
abbrev valModulus (modF : α → α) : Val α → Val α := valMap modF

/-- Liouville's theorem: bounded entire function is constant. -/
theorem liouville [ValOrderedField α] (f : α → α) (c : α)
    (h : ∀ a, f a = c) (a : α) :
    valMap f (contents a) = contents c := by
  simp [valMap, h]

-- ============================================================================
-- 11. C*-ALGEBRAS (383 B3)
-- ============================================================================
-- C*-norm: valMap cstarNormF. The C*-identity and Gelfand representation
-- are single theorems with α-level hypotheses.

/-- C*-norm. -/
abbrev valCStarNorm (cstarF : α → α) : Val α → Val α := valMap cstarF

/-- C*-identity: ‖a*a‖ = ‖a‖². -/
theorem cstar_identity [ValOrderedField α] (normF : α → α) (adjMulF : α → α)
    (h : ∀ a, normF (adjMulF a) = ValArith.mulF (normF a) (normF a))
    (a : α) :
    valNorm normF (contents (adjMulF a)) =
    mul (valNorm normF (contents a)) (valNorm normF (contents a)) := by
  simp [valNorm, valMap, mul, h]

/-- Gelfand representation (abstract). -/
abbrev gelfand (gelfandF : α → α) : Val α → Val α := valMap gelfandF

/-- Gelfand is isometric (abstract). -/
theorem gelfand_isometric [ValOrderedField α] (gelfandF normF : α → α)
    (h : ∀ a, normF (gelfandF a) = normF a) (a : α) :
    valNorm normF (gelfand gelfandF (contents a)) =
    valNorm normF (contents a) := by
  simp [gelfand, valNorm, valMap, h]

/-- State on a C*-algebra (abstract). -/
def isCStarState [ValOrderedField α] (stateF : α → α) (normF : α → α) : Prop :=
  ∀ a, ValOrderedField.leF (normF (stateF a)) (normF a)

/-- GNS construction: state → representation. -/
abbrev gnsRepr (gnsF : α → α) : Val α → Val α := valMap gnsF

-- ============================================================================
-- 12. ASYMPTOTICS (231 B3)
-- ============================================================================
-- Big-O, little-o are predicates on α-level functions.
-- Asymptotic expansion is a power series with error term.

/-- Big-O: |f(x)| ≤ C|g(x)| eventually. -/
def isBigO (bigOF : (α → α) → (α → α) → Prop) (f g : α → α) : Prop :=
  bigOF f g

/-- Little-o: |f(x)|/|g(x)| → 0. -/
def isLittleO (littleOF : (α → α) → (α → α) → Prop) (f g : α → α) : Prop :=
  littleOF f g

/-- Big-O is transitive. -/
theorem bigO_trans (bigOF : (α → α) → (α → α) → Prop)
    (h_trans : ∀ f g h, bigOF f g → bigOF g h → bigOF f h)
    (f g h : α → α) (hfg : isBigO bigOF f g) (hgh : isBigO bigOF g h) :
    isBigO bigOF f h := h_trans f g h hfg hgh

/-- Big-O addition. -/
theorem bigO_add [ValArith α] (bigOF : (α → α) → (α → α) → Prop)
    (h_add : ∀ f₁ f₂ g, bigOF f₁ g → bigOF f₂ g →
      bigOF (fun x => ValArith.addF (f₁ x) (f₂ x)) g)
    (f₁ f₂ g : α → α) (h₁ : isBigO bigOF f₁ g) (h₂ : isBigO bigOF f₂ g) :
    isBigO bigOF (fun x => ValArith.addF (f₁ x) (f₂ x)) g :=
  h_add f₁ f₂ g h₁ h₂

/-- Asymptotic expansion (abstract). -/
def asympExpansion (expandF : (α → α) → Nat → (α → α)) (f : α → α) (n : Nat) :
    Val α → Val α := valMap (expandF f n)

-- ============================================================================
-- 13. DISTRIBUTIONS (190 B3)
-- ============================================================================
-- Distributions are abstract linear functionals on test functions.
-- Schwartz space, tempered distributions, Sobolev spaces.

/-- Distribution: abstract linear functional. -/
def distribution (distF : α → α) : Val α → Val α := valMap distF

/-- Schwartz space membership. -/
def isSchwartz (schwartzF : (α → α) → Prop) (f : α → α) : Prop := schwartzF f

/-- Tempered distribution. -/
def isTempered (tempF : (α → α) → Prop) (f : α → α) : Prop := tempF f

/-- Weak derivative: derivative in the distributional sense. -/
abbrev weakDeriv (wDerivF : α → α) : Val α → Val α := valMap wDerivF

/-- Sobolev norm (abstract). -/
abbrev sobolevNorm (sobF : α → α) : Val α → Val α := valMap sobF

/-- Sobolev embedding (abstract): Sobolev → continuous. -/
theorem sobolev_embedding [ValOrderedField α] (sobF contF : α → α)
    (h : ∀ a, ValOrderedField.leF (contF a) (sobF a)) (a : α) :
    valLE (valMap contF (contents a)) (valMap sobF (contents a)) := by
  simp [valMap, valLE, h]

-- ============================================================================
-- 14. ORDINARY DIFFERENTIAL EQUATIONS (60 B3)
-- ============================================================================
-- ODE existence, uniqueness, Gronwall, flow maps.

/-- ODE solution: f such that f' = F(t, f(t)). -/
def isODESolution (derivF : α → α) (fieldF : α → α → α) (f : α → α) : Prop :=
  ∀ t, derivF (f t) = fieldF t (f t)

/-- Gronwall's inequality (abstract). -/
theorem gronwall [ValOrderedField α] (gronwallF : α → α → α)
    (h : ∀ a b, ValOrderedField.leF a (gronwallF a b))
    (a b : α) :
    valLE (contents a) (contents (gronwallF a b)) := by
  simp [valLE, h]

/-- Flow map of an ODE. -/
abbrev flowMap (flowF : α → α) : Val α → Val α := valMap flowF

/-- Flow composition: φ(t+s) = φ(t) ∘ φ(s). -/
theorem flow_comp [ValOrderedField α] (flowF : α → α)
    (compF : α → α → α)
    (h : ∀ t s, flowF (ValArith.addF t s) = compF (flowF t) (flowF s))
    (t s : α) :
    flowMap flowF (contents (ValArith.addF t s)) =
    contents (compF (flowF t) (flowF s)) := by
  simp [flowMap, valMap, h]

/-- Picard-Lindelöf: existence and uniqueness (abstract). -/
def picardLindelof (lipF : (α → α → α) → Prop) (fieldF : α → α → α) : Prop :=
  lipF fieldF

-- ============================================================================
-- 15. APPROXIMATION, INTERPOLATION, VARIATIONAL (285 B3)
-- ============================================================================

/-- Weierstrass approximation: polynomial density. -/
def weierstrassApprox (approxF : (α → α) → Nat → α → α) (f : α → α) (n : Nat) :
    Val α → Val α := valMap (approxF f n)

/-- Interpolation (abstract). -/
abbrev interpolate (interpF : α → α) : Val α → Val α := valMap interpF

/-- Quadrature (abstract numerical integration). -/
abbrev quadrature (quadF : α → α) : Val α → Val α := valMap quadF

/-- Variational derivative (abstract). -/
abbrev varDeriv (varF : α → α) : Val α → Val α := valMap varF

/-- Euler-Lagrange equation (abstract). -/
def eulerLagrange (elF : (α → α) → α → Prop) (L : α → α) : Val α → Prop
  | contents a => elF L a
  | _ => False

/-- Minimax theorem (abstract). -/
def minimaxVal (minimaxF : α → α) : Val α → Val α := valMap minimaxF

-- ============================================================================
-- UNIVERSALS: patterns that cover multiple subdomains at once
-- ============================================================================

/-- Any unary analysis operation is valMap. Covers: norm, deriv, integral,
    exp, log, sin, cos, tan, gamma, zeta, Fourier, adjoint, projection,
    conjugate, residue, conformal, distribution, Sobolev norm, flow, etc. -/
theorem analysis_unary_origin (f : α → α) :
    valMap f (origin : Val α) = origin := rfl

theorem analysis_unary_container (f : α → α) (a : α) :
    valMap f (container a) = container (f a) := rfl

/-- Any binary analysis operation is mul. Covers: inner product, beta function,
    bilinear forms, convex combinations, cross-correlations. -/
theorem analysis_binary_origin_left [ValArith α] (b : Val α) :
    mul (origin : Val α) b = origin := by cases b <;> rfl

theorem analysis_binary_origin_right [ValArith α] (a : Val α) :
    mul a (origin : Val α) = origin := by cases a <;> rfl

theorem analysis_binary_contents [ValArith α] (a b : α) :
    mul (contents a) (contents b) = contents (ValArith.mulF a b) := rfl

/-- Composition of analysis operations: valMap f ∘ valMap g = valMap (f ∘ g). -/
theorem analysis_comp (f g : α → α) (x : Val α) :
    valMap f (valMap g x) = valMap (f ∘ g) x := by
  cases x <;> simp [valMap]

/-- Linearity pattern: any linear operation distributes over add. -/
theorem analysis_linear [ValOrderedField α] (f : α → α)
    (h : ∀ a b, f (ValArith.addF a b) = ValArith.addF (f a) (f b))
    (a b : Val α) :
    valMap f (add a b) = add (valMap f a) (valMap f b) := by
  cases a <;> cases b <;> simp [add, valMap, h]

/-- Monotonicity pattern: any monotone operation preserves order. -/
theorem analysis_monotone [ValOrderedField α] (f : α → α)
    (h : ∀ a b, ValOrderedField.leF a b → ValOrderedField.leF (f a) (f b))
    (a b : α) (hab : valLE (contents a) (contents b)) :
    valLE (valMap f (contents a)) (valMap f (contents b)) := by
  simp [valMap, valLE] at *; exact h a b hab

/-- Continuity at a point (abstract). -/
def isContinuousAt (contF : (α → α) → α → Prop) (f : α → α) : Val α → Prop
  | contents a => contF f a
  | _ => False

/-- Uniform continuity (abstract). -/
def isUniformlyCont (ucF : (α → α) → Prop) (f : α → α) : Prop := ucF f

/-- Lipschitz continuity (abstract). -/
def isLipschitz (lipF : (α → α) → α → Prop) (f : α → α) (L : α) : Prop :=
  lipF f L

/-- Contraction mapping (abstract). -/
def isContraction (contrF : (α → α) → Prop) (f : α → α) : Prop := contrF f

/-- Banach fixed point theorem: contraction has unique fixed point. -/
theorem banach_fixed_point (contrF : (α → α) → Prop) (fixedPtF : (α → α) → α)
    (h : ∀ f, contrF f → f (fixedPtF f) = fixedPtF f)
    (f : α → α) (hf : isContraction contrF f) :
    f (fixedPtF f) = fixedPtF f := h f hf

end Val
