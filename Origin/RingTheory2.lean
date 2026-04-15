/-
Released under MIT license.
-/
import Origin.Core

/-!
# Ring Theory on Option α (Core-based)

Val/RingTheory.lean: 479 lines. Ideals, localization, Noetherian,
Dedekind, polynomial, valuation, flat, graded, tensor product.

This version keeps only domain-specific definitions and proofs that
actually use Option.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. IDEALS
-- ============================================================================

structure RingIdeal (α : Type u) [Mul α] [Add α] where
  mem : α → Prop
  add_closed : ∀ a b, mem a → mem b → mem (a + b)
  mul_absorb : ∀ r a, mem a → mem (r * a)

def idealMem [Mul α] [Add α] (I : RingIdeal α) : Option α → Prop
  | some a => I.mem a
  | none => False

@[simp] theorem idealMem_none [Mul α] [Add α] (I : RingIdeal α) :
    idealMem I none = False := rfl

@[simp] theorem idealMem_some [Mul α] [Add α] (I : RingIdeal α) (a : α) :
    idealMem I (some a) = I.mem a := rfl

def isPrime [Mul α] [Add α] (I : RingIdeal α) : Prop :=
  ∀ a b, I.mem (a * b) → I.mem a ∨ I.mem b

def isMaximal [Mul α] [Add α] (I : RingIdeal α) : Prop :=
  ∀ J : RingIdeal α, (∀ a, I.mem a → J.mem a) → (∃ a, J.mem a ∧ ¬I.mem a) →
    ∀ b, J.mem b

-- ============================================================================
-- 2. LOCALIZATION
-- ============================================================================

structure MulSubset (α : Type u) [Mul α] where
  mem : α → Prop
  mul_closed : ∀ a b, mem a → mem b → mem (a * b)

theorem localize_universal (loc f g : α → α) (v : Option α)
    (h : ∀ a, f a = g (loc a)) :
    Option.map f v = Option.map g (Option.map loc v) := by
  cases v <;> simp [h]

-- ============================================================================
-- 3. NOETHERIAN
-- ============================================================================

def isNoetherian [Mul α] [Add α] : Prop :=
  ∀ chain : Nat → RingIdeal α,
    (∀ n, ∀ a, (chain n).mem a → (chain (n + 1)).mem a) →
    ∃ N, ∀ n, N ≤ n → ∀ a, (chain n).mem a ↔ (chain N).mem a

def isArtinian [Mul α] [Add α] : Prop :=
  ∀ chain : Nat → RingIdeal α,
    (∀ n, ∀ a, (chain (n + 1)).mem a → (chain n).mem a) →
    ∃ N, ∀ n, N ≤ n → ∀ a, (chain n).mem a ↔ (chain N).mem a

-- ============================================================================
-- 4. DEDEKIND
-- ============================================================================

def isDedekind [Mul α] [Add α] : Prop :=
  isNoetherian (α := α) ∧ ∀ I : RingIdeal α, isPrime I → isMaximal I

def isPID [Mul α] [Add α] : Prop :=
  ∀ I : RingIdeal α, ∃ g, ∀ a, I.mem a → ∃ r, r * g = a

-- ============================================================================
-- 5. POLYNOMIAL
-- ============================================================================

def isRoot (evalF : α → α) (zero : α) (a : α) : Prop := evalF a = zero

def isIrreducible (irredF : α → Prop) (p : α) : Prop := irredF p

-- ============================================================================
-- 6. GRADED RINGS
-- ============================================================================

def gradeOf (gradeF : α → Nat) : Option α → Option Nat
  | some a => some (gradeF a)
  | none => none

@[simp] theorem gradeOf_none (gradeF : α → Nat) :
    gradeOf gradeF (none : Option α) = none := rfl

@[simp] theorem gradeOf_some (gradeF : α → Nat) (a : α) :
    gradeOf gradeF (some a) = some (gradeF a) := rfl

theorem graded_mul [Mul α] (gradeF : α → Nat)
    (h : ∀ a b, gradeF (a * b) = gradeF a + gradeF b) (a b : α) :
    gradeOf gradeF (some a * some b) = some (gradeF a + gradeF b) := by
  simp [gradeOf, h]

-- ============================================================================
-- 7. TENSOR PRODUCT
-- ============================================================================

variable {β : Type u}

def baseChange (f : α → α) : Option (α × β) → Option (α × β) :=
  Option.map (fun p => (f p.1, p.2))

theorem baseChange_none (f : α → α) :
    baseChange f (none : Option (α × β)) = none := rfl

theorem baseChange_some (f : α → α) (a : α) (b : β) :
    baseChange f (some (a, b)) = some (f a, b) := rfl

theorem restrict_extend (f g : α → α) (v : Option (α × β))
    (h : ∀ a, g (f a) = a) : baseChange g (baseChange f v) = v := by
  cases v with
  | none => rfl
  | some p => simp [baseChange, h]

-- ============================================================================
-- 8. FLAT MODULES
-- ============================================================================

def isFlat (tensorF : α → α → α) : Prop :=
  ∀ f : α → α, (∀ a b, f a = f b → a = b) →
    ∀ a b, tensorF (f a) b = tensorF (f b) b → f a = f b

-- ============================================================================
-- 9. CHINESE REMAINDER
-- ============================================================================

theorem chinese_remainder (q₁ q₂ : α → α) (v : Option α) :
    Option.map (fun a => (q₁ a, q₂ a)) v =
    match Option.map q₁ v, Option.map q₂ v with
    | some x, some y => some (x, y)
    | _, _ => none := by
  cases v <;> simp
