/-
Released under MIT license.
-/
import Origin.Core

/-!
# Geometry on Option α (Core-based)

Val/Geometry.lean: 324 lines. Spec, schemes, sheaves, manifolds,
tangent vectors, Riemannian metric, elliptic curves, de Rham cohomology.

This version keeps only domain-specific definitions and proofs that
actually use Option. Standard `*` `+` `-` notation via Core instances.
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
-- 4. SCHEME MORPHISMS
-- ============================================================================

abbrev schemeMorphism (f : α → α) : Option α → Option α := Option.map f

-- scheme_comp: composition pattern, cases v <;> simp. Derivable from Core.

theorem affine_morphism [Mul α] (f : α → α)
    (h_mul : ∀ a b, f (a * b) = f a * f b) (a b : α) :
    schemeMorphism f (some (a * b)) = some (f a * f b) := by
  simp [schemeMorphism, h_mul]

-- ============================================================================
-- 5. PROJECTIVE SPACE
-- ============================================================================

def projEquiv [Mul α] (a b : α) : Prop := ∃ c : α, a = c * b

-- ============================================================================
-- 6. MANIFOLDS (charts as Option.map)
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

-- tangent_map_comp: composition pattern, derivable from Core.

-- ============================================================================
-- 7. DIFFERENTIAL FORMS + DE RHAM COHOMOLOGY
-- ============================================================================

theorem ext_deriv_sq (dF : α → α) (zero : α)
    (h : ∀ a, dF (dF a) = zero) (a : α) :
    Option.map dF (Option.map dF (some a)) = some zero := by simp [h]

theorem wedge_anticomm [Mul α] [Neg α]
    (h : ∀ a b : α, a * b = -(b * a)) (a b : α) :
    (some a : Option α) * some b = -(some b * some a) := by
  show some (a * b) = some (-(b * a)); exact congrArg some (h a b)

def IsClosed (dF : α → α) (zero : α) (ω : α) : Prop := dF ω = zero
def IsExact (dF : α → α) (ω η : α) : Prop := dF η = ω

theorem exact_implies_closed (dF : α → α) (zero : α)
    (h_sq : ∀ a, dF (dF a) = zero) (ω η : α)
    (h : IsExact dF ω η) : IsClosed dF zero ω := by
  unfold IsClosed; unfold IsExact at h; rw [← h]; exact h_sq η

-- ============================================================================
-- 9. ELLIPTIC CURVES
-- ============================================================================

def IsOnCurve [Mul α] [Add α] (a b x y : α) (sqF cubeF : α → α) : Prop :=
  sqF y = cubeF x + a * x + b

-- ============================================================================
-- 10. GEODESICS
-- ============================================================================

def IsGeodesic (γ : α → α) (metric : α → α → α) : Prop :=
  ∀ t₁ t₂, metric (γ t₁) (γ t₂) = metric t₁ t₂ → True

-- None absorbs: Core.lean's @[simp] set handles all cases.
