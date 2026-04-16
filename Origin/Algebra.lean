/-
Released under MIT license.
-/
import Origin.Core

/-!
# Algebra on Option α (Core-based)

Val/Algebra.lean: 596 lines. Polynomial, module, homological, lattice,
Lie algebra, star algebra, big operators, category theory, GCD, characteristic.

This version keeps only domain-specific definitions and proofs that
actually use Option.
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

-- Star involutive and star_mul_rev: cases v <;> simp [h] / by simp [h].
-- Derivable from Core.

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
-- 7. GCD
-- ============================================================================

theorem gcd_lcm_product [Mul α] (gcdF lcmF : α → α → α)
    (h : ∀ a b, gcdF a b * lcmF a b = a * b) (a b : α) :
    (some (gcdF a b) : Option α) * some (lcmF a b) =
    some a * some b := by simp [h]

-- ============================================================================
-- 8. CHARACTERISTIC
-- ============================================================================

def HasCharP (charF : Nat → α) (zero : α) (p : Nat) : Prop := charF p = zero

-- None absorbs (mul, add): Core.lean's @[simp] set handles all cases.
