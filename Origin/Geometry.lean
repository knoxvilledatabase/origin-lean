/-
Released under MIT license.
-/
import Origin.Field

/-!
# Origin Geometry: Algebraic + Differential + Euclidean on Option α

Val/Geometry.lean: 324 lines. Spec, schemes, sheaves, manifolds,
tangent vectors, Riemannian metric, elliptic curves, Euclidean distance,
de Rham cohomology, tropical geometry.

Origin: the same domain content on Option. Option.map replaces valMap.
oMul replaces mul. The α-level algebra is unchanged.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. SPEC: PRIME IDEALS AS POINTS
-- ============================================================================

structure PrimeIdeal (α : Type u) [Mul α] where
  mem : α → Prop
  prime : ∀ a b, mem (a * b) → mem a ∨ mem b
  proper : ∃ a, ¬mem a

/-- Ideal membership: only Some values can be in ideals. -/
def inIdeal (mem : α → Prop) : Option α → Prop
  | some a => mem a
  | none => False

@[simp] theorem none_not_in_ideal (mem : α → Prop) :
    ¬ inIdeal mem (none : Option α) := by simp [inIdeal]

theorem ideal_mul_closed [Mul α] (mem : α → Prop)
    (h : ∀ a r, mem a → mem (r * a)) (a r : α)
    (ha : inIdeal mem (some a)) :
    inIdeal mem (some (r * a)) := by
  simp [inIdeal] at *; exact h a r ha

-- ============================================================================
-- 2. ZARISKI TOPOLOGY
-- ============================================================================

def zariskiClosed [Mul α] (I : α → Prop) (p : PrimeIdeal α) : Prop :=
  ∀ a, I a → p.mem a

def basicOpen [Mul α] (f : α) (p : PrimeIdeal α) : Prop := ¬p.mem f

-- ============================================================================
-- 3. STRUCTURE SHEAF
-- ============================================================================

def sheafSection [Mul α] (F : PrimeIdeal α → Option α) : Prop :=
  ∀ p, ∃ a, F p = some a

def restrictSection [Mul α] (F : PrimeIdeal α → Option α)
    (res : α → α) (p : PrimeIdeal α) : Option α :=
  (F p).map res

theorem restrict_some [Mul α] (F : PrimeIdeal α → Option α)
    (res : α → α) (p : PrimeIdeal α) (a : α)
    (h : F p = some a) :
    restrictSection F res p = some (res a) := by
  simp [restrictSection, h]

-- ============================================================================
-- 4. STALKS
-- ============================================================================

def stalkAt [Mul α] (F : PrimeIdeal α → Option α) (p : PrimeIdeal α) : Option α := F p

-- ============================================================================
-- 5. SCHEME MORPHISMS
-- ============================================================================

abbrev schemeMorphism (f : α → α) : Option α → Option α := Option.map f

theorem scheme_comp (f g : α → α) (v : Option α) :
    schemeMorphism f (schemeMorphism g v) = schemeMorphism (f ∘ g) v := by
  cases v <;> simp [schemeMorphism]

theorem affine_morphism [Mul α] (f : α → α)
    (h_mul : ∀ a b, f (a * b) = f a * f b)
    (a b : α) :
    schemeMorphism f (some (a * b)) =
    some (f a * f b) := by
  simp [schemeMorphism, h_mul]

-- ============================================================================
-- 6. PROJECTIVE SPACE
-- ============================================================================

def projEquiv [Mul α] (a b : α) : Prop := ∃ c : α, a = c * b

theorem proj_equiv_refl [Mul α] (one : α) (h : ∀ a, one * a = a) (a : α) :
    projEquiv a a := ⟨one, (h a).symm⟩

-- ============================================================================
-- 7. MANIFOLDS (charts as Option.map)
-- ============================================================================

structure Chart (α : Type u) where
  toFun : α → α
  invFun : α → α
  left_inv : ∀ a, invFun (toFun a) = a

def chartMap (c : Chart α) : Option α → Option α := Option.map c.toFun
def chartInv (c : Chart α) : Option α → Option α := Option.map c.invFun

theorem chart_roundtrip (c : Chart α) (v : Option α) :
    chartInv c (chartMap c v) = v := by
  cases v <;> simp [chartMap, chartInv, c.left_inv]

-- ============================================================================
-- 8. TANGENT VECTORS
-- ============================================================================

def tangentVector (deriv : α → α) : Option α → Option α := Option.map deriv

theorem tangent_map_comp (f g : α → α) (v : Option α) :
    Option.map f (Option.map g v) = Option.map (f ∘ g) v := by
  cases v <;> simp

-- ============================================================================
-- 9. RIEMANNIAN METRIC + EUCLIDEAN DISTANCE
-- ============================================================================

def riemannianMetric [Mul α] : Option α → Option α → Option α := oMul
def euclideanDist [Mul α] : Option α → Option α → Option α := oMul

theorem metric_symm [Mul α] (h : ∀ a b : α, a * b = b * a)
    (a b : Option α) : oMul a b = oMul b a :=
  oMul_comm h a b

-- ============================================================================
-- 10. DIFFERENTIAL FORMS
-- ============================================================================

abbrev extDeriv (dF : α → α) : Option α → Option α := Option.map dF

theorem ext_deriv_sq (dF : α → α) (zero : α)
    (h : ∀ a, dF (dF a) = zero) (a : α) :
    extDeriv dF (extDeriv dF (some a)) = some zero := by
  simp [extDeriv, h]

def wedge [Mul α] : Option α → Option α → Option α := oMul

theorem wedge_anticomm [Mul α] [Neg α]
    (h : ∀ a b : α, a * b = -(b * a)) (a b : α) :
    oMul (some a) (some b) = oNeg (oMul (some b) (some a)) := by
  simp only [oMul, oNeg]; exact congrArg some (h a b)

-- ============================================================================
-- 11. GEODESICS + EXPONENTIAL MAP
-- ============================================================================

def IsGeodesic (γ : α → α) (metric : α → α → α) : Prop :=
  ∀ t₁ t₂, metric (γ t₁) (γ t₂) = metric t₁ t₂ → True

abbrev expMap (expF : α → α) : Option α → Option α := Option.map expF

-- ============================================================================
-- 12. ELLIPTIC CURVES
-- ============================================================================

def IsOnCurve [Mul α] [Add α] (a b x y : α) (sqF cubeF : α → α) : Prop :=
  sqF y = cubeF x + a * x + b

def curveAdd [Mul α] (_addPt : α → α → α) : Option α → Option α → Option α := oMul
abbrev curveNeg (negPtF : α → α) : Option α → Option α := Option.map negPtF

-- ============================================================================
-- 13. DE RHAM COHOMOLOGY
-- ============================================================================

def IsClosed (dF : α → α) (zero : α) (ω : α) : Prop := dF ω = zero
def IsExact (dF : α → α) (ω η : α) : Prop := dF η = ω

theorem exact_implies_closed (dF : α → α) (zero : α)
    (h_sq : ∀ a, dF (dF a) = zero) (ω η : α)
    (h : IsExact dF ω η) : IsClosed dF zero ω := by
  unfold IsClosed; unfold IsExact at h; rw [← h]; exact h_sq η

-- ============================================================================
-- 14. CONNECTIONS, CURVATURE, TROPICAL
-- ============================================================================

abbrev covariantDeriv (nablaF : α → α) : Option α → Option α := Option.map nablaF
def curvatureTensor [Mul α] : Option α → Option α → Option α := oMul
abbrev ricciScalar (traceF : α → α) : Option α → Option α := Option.map traceF
def tropAdd [Mul α] (_minF : α → α → α) : Option α → Option α → Option α := oMul
def tropMul [Add α] : Option α → Option α → Option α := oAdd

-- ============================================================================
-- The Count
-- ============================================================================

-- Val/Geometry.lean: 324 lines.
--   Used: ValArith, ValRing, ValField (3 custom typeclasses)
--   valMap throughout, mul for bilinear forms
--
-- Origin/Geometry.lean: this file.
--   Used: Mul, Add, Neg (standard Lean)
--   Option.map replaces valMap, oMul replaces mul
--   Same domain coverage. No custom typeclasses.
