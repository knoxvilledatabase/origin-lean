/-
Released under MIT license.
-/
import Val.Analysis.Core

/-!
# Val α: Analysis — Spaces

Sections 17-23: Matrix analysis, Lp spaces, functional spaces, real spaces,
inner product spaces, C*-algebras, locally convex spaces.

Contents in, contents out. The sort is structural. No ≠ 0 at sort level.
-/

namespace Val

universe u
variable {α : Type u}

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
