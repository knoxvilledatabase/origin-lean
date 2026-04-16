/-
Released under MIT license.
-/
import Origin.Core

/-!
# Number Theory on Option α (Core-based)

Val/NumberTheory.lean: 667 lines. p-adics, number fields, modular forms,
L-series, arithmetic functions, Legendre symbol, FLT, cyclotomic.

This version keeps only domain-specific definitions and proofs that
actually use Option.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. P-ADIC VALUATIONS
-- ============================================================================

theorem padic_val_mul [Mul α] [Add α] (vpF : α → α)
    (h : ∀ a b, vpF (a * b) = vpF a + vpF b) (a b : α) :
    Option.map vpF (some a * some b) =
    Option.map vpF (some a) + Option.map vpF (some b) := by simp [h]

def isPadicInt (vpF : α → α) (leF : α → α → Prop) (zeroV : α) : Option α → Prop
  | some a => leF zeroV (vpF a)
  | none => False

-- ============================================================================
-- 2. NUMBER FIELD
-- ============================================================================

def isAlgInt (isIntF : α → Prop) : Option α → Prop
  | some a => isIntF a
  | none => False

-- atkin_lehner_involution: involution pattern, derivable from Core.

-- ============================================================================
-- 3. MODULAR FORMS
-- ============================================================================

theorem hecke_eigenform [Mul α] (heckeF : α → α) (f lambda : α)
    (h : heckeF f = lambda * f) :
    Option.map heckeF (some f) = some (lambda * f) := by simp [h]

-- ============================================================================
-- 4. ARITHMETIC FUNCTIONS
-- ============================================================================

def isMultiplicative (f : α → α) (mulα : α → α → α) (coprime : α → α → Prop) : Prop :=
  ∀ m n, coprime m n → f (mulα m n) = mulα (f m) (f n)

-- ============================================================================
-- 5. LEGENDRE SYMBOL
-- ============================================================================

def isQuadResidue (qrF : α → Prop) : Option α → Prop
  | some a => qrF a
  | none => False

-- ============================================================================
-- 6. FLT AND REGULAR PRIMES
-- ============================================================================

def isRegularPrime (dividesF : α → α → Prop) (classNumF : α → α) : α → Prop :=
  fun p => ¬ dividesF p (classNumF p)

-- ============================================================================
-- 7. Z[√d]
-- ============================================================================

-- zsqrtd_conj_involution: involution pattern, derivable from Core.

-- ============================================================================
-- 8. CYCLOTOMIC
-- ============================================================================

def isPrimitiveRoot (orderF : α → α) (n : α) : Option α → Prop
  | some a => orderF a = n
  | none => False

-- ============================================================================
-- 9. SUM OF SQUARES
-- ============================================================================

def isSumTwoSquares [Mul α] [Add α] (n a b : α) : Prop :=
  a * a + b * b = n

def isSumFourSquares [Mul α] [Add α] (n a b c d : α) : Prop :=
  (a * a + b * b) + (c * c + d * d) = n

-- ============================================================================
-- 10. PRIMALITY
-- ============================================================================

def isPrime (primeF : α → Prop) : Option α → Prop
  | some a => primeF a
  | none => False

-- ============================================================================
-- 11. ASYMPTOTICS
-- ============================================================================

def isBigO (leF : α → α → Prop) (fF gF cF : α → α) : Prop :=
  ∀ x, leF (fF x) (cF (gF x))
