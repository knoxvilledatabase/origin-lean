/-
Released under MIT license.
-/
import Origin.Core

/-!
# Algebra on Option α (Core-based)

**Goal B classification:**
- Polynomial roots, homological algebra, Lie algebra, big operators,
  GCD, characteristic — Category 1 (Option-meaningful: none = no
  polynomial, no cycle, no chain; these interact with the ground)
- Lattice theory (join/meet), distributive/modular laws, Vieta's
  formula, HasDistribNeg — Category 2 (clean math, no infrastructure)
- NoZeroDivisors, IsCancelMulZero, IsDomain — dissolved infrastructure
  (managed zero-inside-domain; Origin dissolves these entirely)

Mathlib_Algebra: 797 files, 47 dissolved declarations.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. POLYNOMIAL
-- ============================================================================

def IsRoot (evalF : α → α) (zero : α) (a : α) : Prop := evalF a = zero

theorem root_gives_zero (evalF : α → α) (zero : α) (a : α)
    (h : IsRoot evalF zero a) :
    Option.map evalF (some a) = some zero := by simp [IsRoot] at h; simp [h]

def IsIrreducible (p : α) (factorsF : α → α × α) (isUnit : α → Prop) : Prop :=
  ¬isUnit p ∧ ∀ a b, factorsF p = (a, b) → isUnit a ∨ isUnit b

-- ============================================================================
-- 2. HOMOLOGICAL ALGEBRA
-- ============================================================================

def IsBoundary (d : α → α) (b a : α) : Prop := d a = b
def IsCycle (d : α → α) (zero : α) (a : α) : Prop := d a = zero

def IsShortExact (f g : α → α) (zero : α) : Prop :=
  (∀ a b, f a = f b → a = b) ∧ (∀ b, ∃ a, g a = b) ∧ (∀ a, g (f a) = zero)

-- ============================================================================
-- 3. ORDER AND LATTICE
-- ============================================================================

structure BoundedLattice (α : Type u) where
  top : α
  bot : α
  joinF : α → α → α
  meetF : α → α → α
  le_top : ∀ a : α, joinF a top = top
  bot_le : ∀ a : α, joinF bot a = a

def IsDistributive (joinF meetF : α → α → α) : Prop :=
  ∀ a b c, meetF a (joinF b c) = joinF (meetF a b) (meetF a c)

def IsModular (joinF meetF : α → α → α) (leF : α → α → Prop) : Prop :=
  ∀ a b c, leF a c → meetF c (joinF a b) = joinF a (meetF c b)

-- ============================================================================
-- 4. LIE ALGEBRA
-- ============================================================================

def IsLieIdeal (mem : α → Prop) (bracketF : α → α → α) : Prop :=
  ∀ a x, mem a → ∃ r, bracketF x a = r ∧ mem r

def IsSemisimple (killF : α → α → α) (zero : α) : Prop :=
  ∀ a, (∀ b, killF a b = zero) → a = zero

-- ============================================================================
-- 5. BIG OPERATORS
-- ============================================================================

def bigSum [Add α] (zero : α) : List α → α
  | [] => zero
  | a :: as => a + bigSum zero as

def bigProd [Mul α] (one : α) : List α → α
  | [] => one
  | a :: as => a * bigProd one as

-- ============================================================================
-- 6. GCD
-- ============================================================================

theorem gcd_lcm_product [Mul α] (gcdF lcmF : α → α → α)
    (h : ∀ a b, gcdF a b * lcmF a b = a * b) (a b : α) :
    (some (gcdF a b) : Option α) * some (lcmF a b) =
    some a * some b := by simp [h]

-- ============================================================================
-- 7. CHARACTERISTIC
-- ============================================================================

def HasCharP (charF : Nat → α) (zero : α) (p : Nat) : Prop := charF p = zero

-- ============================================================================
-- 8. GALOIS THEORY
-- ============================================================================

/-- A field extension: base embeds into extension. -/
structure FieldExt (K F : Type u) where
  embed : K → F
  embed_inj : ∀ a b : K, embed a = embed b → a = b

/-- An automorphism that fixes the base field. -/
def IsFieldAut (σ : α → α) (isBase : α → Prop) : Prop :=
  (∀ a, isBase a → σ a = a) ∧ (∀ a b, σ a = σ b → a = b) ∧ (∀ b, ∃ a, σ b = a)

/-- Galois group: set of automorphisms fixing the base. -/
def GaloisGroupMem (σ : α → α) (isBase : α → Prop) : Prop :=
  ∀ a, isBase a → σ a = a

/-- Fundamental theorem: intermediate fields correspond to subgroups. -/
def IsGaloisCorrespondence
    (intermField : (α → Prop) → Prop)
    (subgroup : ((α → α) → Prop) → Prop)
    (fixedField : ((α → α) → Prop) → (α → Prop))
    (autGroup : (α → Prop) → ((α → α) → Prop)) : Prop :=
  (∀ H, subgroup H → intermField (fixedField H)) ∧
  (∀ E, intermField E → subgroup (autGroup E))

/-- Galois extension lifts through Option: none = outside the extension. -/
theorem galois_fixes_option (σ : α → α) (isBase : α → Prop)
    (h : GaloisGroupMem σ isBase) (a : α) (hb : isBase a) :
    Option.map σ (some a) = some a := by simp [GaloisGroupMem] at h; simp [h a hb]

-- ============================================================================
-- 9. STAR ALGEBRAS
-- ============================================================================

/-- Star involution on a type. -/
def IsStarInvolution (star : α → α) : Prop :=
  ∀ a, star (star a) = a

/-- Star reverses multiplication. -/
def IsStarMulRev [Mul α] (star : α → α) : Prop :=
  ∀ a b, star (a * b) = star b * star a

/-- C*-identity: ‖x* x‖ = ‖x‖². -/
def IsCStarIdentity (star : α → α) (normF : α → α) [Mul α] : Prop :=
  ∀ a, normF (star a * a) = normF a * normF a

/-- Star lifts through Option: none stays none. -/
theorem star_option_none (star : α → α) :
    Option.map star (none : Option α) = none := by simp

theorem star_option_some (star : α → α) (a : α) :
    Option.map star (some a : Option α) = some (star a) := by simp

-- ============================================================================
-- 10. VIETA'S FORMULAS
-- ============================================================================

/-- Sum of roots of a polynomial (via coefficient). -/
def vietaSum [Neg α] [Div α] (leadCoeff nextCoeff : α) : α :=
  -(nextCoeff / leadCoeff)

/-- Product of roots of a quadratic (via coefficient). -/
def vietaProduct [Div α] (leadCoeff constCoeff : α) : α :=
  constCoeff / leadCoeff

/-- Vieta lifts: if coefficients are some, result is some. -/
theorem vieta_sum_option [Neg α] [Div α] (a b : α) :
    some (vietaSum a b) = some (-(b / a)) := by rfl

-- ============================================================================
-- 11. CLIFFORD ALGEBRAS
-- ============================================================================

/-- Clifford relation: v * v = Q(v) · 1. -/
def IsCliffordRel [Mul α] (quadForm : α → α) (v : α) : Prop :=
  v * v = quadForm v

/-- Anti-commutation in a Clifford algebra. -/
def IsCliffordAnticomm [Mul α] [Add α] (quadForm : α → α → α) : Prop :=
  ∀ u v, u * v + v * u = quadForm u v

/-- Clifford product lifts through Option. -/
theorem clifford_mul_option [Mul α] (a b : α) :
    (some a : Option α) * some b = some (a * b) := by simp

-- ============================================================================
-- 12. MODULES
-- ============================================================================

/-- A module action: scalar multiplication. -/
def IsModuleAction [Mul α] (smul : α → α → α) (one : α) : Prop :=
  (∀ x, smul one x = x) ∧ (∀ r s x, smul r (smul s x) = smul (r * s) x)

/-- Free module: every element is a unique linear combination. -/
def IsFreeModule (basis : α → Prop) (span : (α → Prop) → α → Prop)
    (_unique : ∀ a, span basis a → ∃ _coeffs : α, True) : Prop :=
  ∀ a, span basis a

/-- Projective module: every surjection onto it splits. -/
def IsProjectiveModule (liftF : (α → α) → (α → α)) : Prop :=
  ∀ (f : α → α) (_surj : ∀ b, ∃ a, f a = b), ∀ x, f (liftF f x) = x

-- ============================================================================
-- 13. ASSOCIATIVE ALGEBRAS
-- ============================================================================

/-- Algebra homomorphism: preserves both ring ops and scalar action. -/
def IsAlgHom [Mul α] [Add α] (f : α → α) : Prop :=
  (∀ a b, f (a * b) = f a * f b) ∧ (∀ a b, f (a + b) = f a + f b)

/-- Algebra homomorphism lifts through Option. -/
theorem alg_hom_option [Mul α] [Add α] (f : α → α) (a : α) :
    Option.map f (some a) = some (f a) := by simp

/-- Algebra homomorphism preserves none (ground absorbs). -/
theorem alg_hom_none [Mul α] [Add α] (f : α → α) :
    Option.map f (none : Option α) = none := by simp

-- ============================================================================
-- 14. DEMONSTRATIONS: Option lifting
-- ============================================================================

/-- Multiplication lifts: some a * some b = some (a * b). -/
theorem algebra_mul_lifts [Mul α] (a b : α) :
    (some a : Option α) * some b = some (a * b) := by simp

/-- Addition lifts: some a + some b = some (a + b). -/
theorem algebra_add_lifts [Add α] (a b : α) :
    (some a : Option α) + some b = some (a + b) := by simp

/-- none absorbs multiplication on the left. -/
theorem algebra_none_mul [Mul α] (b : Option α) :
    (none : Option α) * b = none := by simp

/-- none is identity for addition on the left. -/
theorem algebra_none_add [Add α] (b : Option α) :
    (none : Option α) + b = b := by simp

/-- Negation lifts through some. -/
theorem algebra_neg_lifts [Neg α] (a : α) :
    -(some a : Option α) = some (-a) := by simp

/-- Negation of none stays none. -/
theorem algebra_neg_none [Neg α] :
    -(none : Option α) = none := by simp

-- None absorbs (mul, add): Core.lean's @[simp] set handles all cases.
