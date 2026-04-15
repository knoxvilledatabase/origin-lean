/-
Released under MIT license.
-/
import Origin.Foundation

/-!
# Origin Ring: Ring Laws on Option α

Val needed 461 lines across three files (Foundation, Arith, Ring)
before a single domain theorem. Origin needs this file.

The ring laws on α lift through Option in two cases (none/some)
instead of three (origin/container/contents). No custom type.
No class hierarchy. Just Option.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- Operations
-- ============================================================================

def oMul [Mul α] : Option α → Option α → Option α
  | none, _        => none
  | _, none        => none
  | some a, some b => some (a * b)

def oAdd [Add α] : Option α → Option α → Option α
  | none, x        => x
  | x, none        => x
  | some a, some b => some (a + b)

def oNeg [Neg α] : Option α → Option α
  | none   => none
  | some a => some (-a)

-- ============================================================================
-- Simp Set
-- ============================================================================

@[simp] theorem oMul_none_left [Mul α] (b : Option α) : oMul none b = none := by
  cases b <;> rfl
@[simp] theorem oMul_none_right [Mul α] (a : Option α) : oMul a none = none := by
  cases a <;> rfl
@[simp] theorem oMul_some [Mul α] (a b : α) : oMul (some a) (some b) = some (a * b) := rfl

@[simp] theorem oAdd_none_left [Add α] (b : Option α) : oAdd none b = b := by
  cases b <;> rfl
@[simp] theorem oAdd_none_right [Add α] (a : Option α) : oAdd a none = a := by
  cases a <;> rfl
@[simp] theorem oAdd_some [Add α] (a b : α) : oAdd (some a) (some b) = some (a + b) := rfl

@[simp] theorem oNeg_none [Neg α] : oNeg (none : Option α) = none := rfl
@[simp] theorem oNeg_some [Neg α] (a : α) : oNeg (some a) = some (-a) := rfl

-- ============================================================================
-- Ring Laws: Two Cases Instead of Three
-- ============================================================================

theorem oMul_assoc [Mul α]
    (h : ∀ a b c : α, a * b * c = a * (b * c))
    (a b c : Option α) :
    oMul (oMul a b) c = oMul a (oMul b c) := by
  cases a <;> cases b <;> cases c <;> simp [oMul, h]

theorem oMul_comm [Mul α]
    (h : ∀ a b : α, a * b = b * a)
    (a b : Option α) :
    oMul a b = oMul b a := by
  cases a <;> cases b <;> simp [oMul, h]

theorem oAdd_assoc [Add α]
    (h : ∀ a b c : α, a + b + c = a + (b + c))
    (a b c : Option α) :
    oAdd (oAdd a b) c = oAdd a (oAdd b c) := by
  cases a <;> cases b <;> cases c <;> simp [oAdd, h]

theorem oAdd_comm [Add α]
    (h : ∀ a b : α, a + b = b + a)
    (a b : Option α) :
    oAdd a b = oAdd b a := by
  cases a <;> cases b <;> simp [oAdd, h]

theorem oLeft_distrib [Mul α] [Add α]
    (h : ∀ a b c : α, a * (b + c) = a * b + a * c)
    (a b c : Option α) :
    oMul a (oAdd b c) = oAdd (oMul a b) (oMul a c) := by
  cases a <;> cases b <;> cases c <;> simp [oMul, oAdd, h]

theorem oRight_distrib [Mul α] [Add α]
    (h : ∀ a b c : α, (a + b) * c = a * c + b * c)
    (a b c : Option α) :
    oMul (oAdd a b) c = oAdd (oMul a c) (oMul b c) := by
  cases a <;> cases b <;> cases c <;> simp [oMul, oAdd, h]

theorem oNeg_mul [Mul α] [Neg α]
    (h : ∀ a b : α, -a * b = -(a * b))
    (a b : Option α) :
    oMul (oNeg a) b = oNeg (oMul a b) := by
  cases a <;> cases b <;> simp [oMul, oNeg, h]

theorem oMul_neg [Mul α] [Neg α]
    (h : ∀ a b : α, a * -b = -(a * b))
    (a b : Option α) :
    oMul a (oNeg b) = oNeg (oMul a b) := by
  cases a <;> cases b <;> simp [oMul, oNeg, h]

theorem oNeg_neg [Neg α]
    (h : ∀ a : α, -(-a) = a)
    (a : Option α) :
    oNeg (oNeg a) = a := by
  cases a <;> simp [oNeg, h]

-- ============================================================================
-- The Count
-- ============================================================================

-- Val: 461 lines, 3 files, 1 custom type, 5-level class hierarchy.
-- Origin: this file. Option. 9 lifted laws. Each one: cases <;> simp.
--
-- The five-level hierarchy (ValArith → ValRing → ValField →
-- ValOrderedField → ValModule) managed the ground being inside.
-- Option puts it outside. The hierarchy has nothing to manage.
--
-- The ground absorbs (none × x = none). The parts compute
-- (some a × some b = some (a * b)). Two pattern matches.
-- That's what 461 lines were doing.
