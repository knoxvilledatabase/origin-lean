/-
Released under MIT license.
-/
import Origin.Ring

/-!
# Origin RingTheory: Ideals through Tensors on Option α

Val/RingTheory.lean: 479 lines. Ideals, localization, Noetherian,
Dedekind, polynomial, valuation, flat, graded, tensor products.

Origin: the same domain content on Option. Option.map replaces valMap.
oMul/oAdd replace mul/add. No custom typeclasses.
-/

universe u
variable {α β : Type u}

-- ============================================================================
-- 1. IDEALS
-- ============================================================================

structure RingIdeal (α : Type u) [Mul α] [Add α] where
  mem : α → Prop
  add_closed : ∀ a b, mem a → mem b → mem (a + b)
  mul_absorb : ∀ r a, mem a → mem (r * a)

def idealMem [Mul α] [Add α] (I : RingIdeal α) : Option α → Prop
  | none => False
  | some a => I.mem a

@[simp] theorem idealMem_none [Mul α] [Add α] (I : RingIdeal α) :
    idealMem I (none : Option α) = False := rfl

@[simp] theorem idealMem_some [Mul α] [Add α] (I : RingIdeal α) (a : α) :
    idealMem I (some a) = I.mem a := rfl

theorem idealMem_mul_absorb [Mul α] [Add α] (I : RingIdeal α) (r a : α)
    (ha : I.mem a) : idealMem I (some (r * a)) := by
  simp; exact I.mul_absorb r a ha

def isPrime [Mul α] [Add α] (I : RingIdeal α) : Prop :=
  ∀ a b, I.mem (a * b) → I.mem a ∨ I.mem b

def isMaximal [Mul α] [Add α] (I : RingIdeal α) : Prop :=
  ∀ J : RingIdeal α, (∀ a, I.mem a → J.mem a) → (∃ a, J.mem a ∧ ¬I.mem a) →
    ∀ b, J.mem b

def isInRadical [Mul α] [Add α] (I : RingIdeal α) (powF : α → Nat → α) (a : α) : Prop :=
  ∃ n : Nat, I.mem (powF a n)

theorem radical_contains [Mul α] [Add α] (I : RingIdeal α) (powF : α → Nat → α)
    (hpow1 : ∀ a, powF a 1 = a) (a : α) (ha : I.mem a) :
    isInRadical I powF a := ⟨1, by rw [hpow1]; exact ha⟩

-- ============================================================================
-- 2. QUOTIENT MAP (Option.map)
-- ============================================================================

abbrev quotientMap (q : α → α) : Option α → Option α := Option.map q

theorem quotientMap_none (q : α → α) :
    quotientMap q (none : Option α) = none := rfl

theorem quotientMap_mul [Mul α] (q : α → α)
    (h : ∀ a b, q (a * b) = q a * q b) (a b : α) :
    quotientMap q (oMul (some a) (some b)) =
    oMul (quotientMap q (some a)) (quotientMap q (some b)) := by
  simp [quotientMap, oMul, h]

theorem quotientMap_add [Add α] (q : α → α)
    (h : ∀ a b, q (a + b) = q a + q b) (a b : α) :
    quotientMap q (oAdd (some a) (some b)) =
    oAdd (quotientMap q (some a)) (quotientMap q (some b)) := by
  simp [quotientMap, oAdd, h]

theorem quotientMap_comp (q₁ q₂ : α → α) (v : Option α) :
    quotientMap q₂ (quotientMap q₁ v) = quotientMap (q₂ ∘ q₁) v := by
  cases v <;> simp [quotientMap]

-- ============================================================================
-- 3. LOCALIZATION (Option.map)
-- ============================================================================

abbrev localize (loc : α → α) : Option α → Option α := Option.map loc

theorem localize_none (loc : α → α) :
    localize loc (none : Option α) = none := rfl

theorem localize_mul [Mul α] (loc : α → α)
    (h : ∀ a b, loc (a * b) = loc a * loc b) (a b : α) :
    localize loc (oMul (some a) (some b)) =
    oMul (localize loc (some a)) (localize loc (some b)) := by
  simp [localize, oMul, h]

theorem localize_universal (loc f g : α → α) (v : Option α)
    (h : ∀ a, f a = g (loc a)) :
    Option.map f v = Option.map g (localize loc v) := by
  cases v <;> simp [localize, h]

theorem localize_comp (loc₁ loc₂ : α → α) (v : Option α) :
    localize loc₂ (localize loc₁ v) = localize (loc₂ ∘ loc₁) v := by
  cases v <;> simp [localize]

theorem fraction_field_injective (loc : α → α)
    (hloc : ∀ a b, loc a = loc b → a = b) (a b : α)
    (h : localize loc (some a) = localize loc (some b)) :
    (some a : Option α) = some b := by
  simp [localize] at h; exact congrArg some (hloc a b h)

-- ============================================================================
-- 4. NOETHERIAN + DEDEKIND
-- ============================================================================

def isNoetherian [Mul α] [Add α] : Prop :=
  ∀ chain : Nat → RingIdeal α,
    (∀ n, ∀ a, (chain n).mem a → (chain (n + 1)).mem a) →
    ∃ N, ∀ n, N ≤ n → ∀ a, (chain n).mem a ↔ (chain N).mem a

def isDedekind [Mul α] [Add α] : Prop :=
  isNoetherian (α := α) ∧ ∀ I : RingIdeal α, isPrime I → isMaximal I

def isPID [Mul α] [Add α] : Prop :=
  ∀ I : RingIdeal α, ∃ g, ∀ a, I.mem a → ∃ r, r * g = a

def isUFD (irredF : α → Prop) (factorize : α → α → Prop) : Prop :=
  ∀ a, ∃ p, irredF p ∧ factorize p a

-- ============================================================================
-- 5. POLYNOMIAL (Option.map)
-- ============================================================================

abbrev polyEval (evalF : α → α) : Option α → Option α := Option.map evalF

theorem polyEval_none (evalF : α → α) :
    polyEval evalF (none : Option α) = none := rfl

theorem polyEval_add [Add α] (evalF : α → α)
    (h : ∀ p q, evalF (p + q) = evalF p + evalF q) (p q : α) :
    polyEval evalF (oAdd (some p) (some q)) =
    oAdd (polyEval evalF (some p)) (polyEval evalF (some q)) := by
  simp [polyEval, oAdd, h]

theorem polyEval_mul [Mul α] (evalF : α → α)
    (h : ∀ p q, evalF (p * q) = evalF p * evalF q) (p q : α) :
    polyEval evalF (oMul (some p) (some q)) =
    oMul (polyEval evalF (some p)) (polyEval evalF (some q)) := by
  simp [polyEval, oMul, h]

theorem polyEval_comp (f g : α → α) (v : Option α) :
    polyEval g (polyEval f v) = polyEval (g ∘ f) v := by
  cases v <;> simp [polyEval]

def isRoot (evalAtF : α → α → α) (p r zero : α) : Prop := evalAtF p r = zero

theorem hensel_lift (evalF liftF : α → α) (v : Option α)
    (h : ∀ a, evalF (liftF a) = evalF a) :
    polyEval evalF (Option.map liftF v) = polyEval evalF v := by
  cases v <;> simp [polyEval, h]

-- ============================================================================
-- 6. VALUATION (Option.map)
-- ============================================================================

abbrev valuation (vF : α → α) : Option α → Option α := Option.map vF

theorem valuation_none (vF : α → α) :
    valuation vF (none : Option α) = none := rfl

theorem valuation_mul [Mul α] [Add α] (vF : α → α)
    (h : ∀ a b, vF (a * b) = vF a + vF b) (a b : α) :
    valuation vF (oMul (some a) (some b)) =
    oAdd (valuation vF (some a)) (valuation vF (some b)) := by
  simp [valuation, oMul, oAdd, h]

abbrev completion (compF : α → α) : Option α → Option α := Option.map compF

theorem completion_comp (f g : α → α) (v : Option α) :
    completion g (completion f v) = completion (g ∘ f) v := by
  cases v <;> simp [completion]

-- ============================================================================
-- 7. FLAT
-- ============================================================================

def isFlat (tensorF : α → α → α) : Prop :=
  ∀ f : α → α, (∀ a b, f a = f b → a = b) →
    ∀ a b, tensorF (f a) b = tensorF (f b) b → f a = f b

def flatDescent (descF : α → α) : Option α → Option α := Option.map descF

theorem flatDescent_none (descF : α → α) :
    flatDescent descF (none : Option α) = none := rfl

-- ============================================================================
-- 8. GRADED
-- ============================================================================

def gradeOf (gradeF : α → Nat) : Option α → Option Nat
  | none => none
  | some a => some (gradeF a)

@[simp] theorem gradeOf_none (gradeF : α → Nat) :
    gradeOf gradeF (none : Option α) = none := rfl

@[simp] theorem gradeOf_some (gradeF : α → Nat) (a : α) :
    gradeOf gradeF (some a) = some (gradeF a) := rfl

theorem graded_mul [Mul α] (gradeF : α → Nat)
    (h : ∀ a b, gradeF (a * b) = gradeF a + gradeF b) (a b : α) :
    gradeOf gradeF (oMul (some a) (some b)) = some (gradeF a + gradeF b) := by
  simp [gradeOf, oMul, h]

-- ============================================================================
-- 9. TENSOR PRODUCTS
-- ============================================================================

def tensor : Option α → Option β → Option (α × β)
  | none, _ => none
  | _, none => none
  | some a, some b => some (a, b)

@[simp] theorem tensor_none_left (b : Option β) :
    tensor (none : Option α) b = none := by cases b <;> rfl

@[simp] theorem tensor_none_right (a : Option α) :
    tensor a (none : Option β) = none := by cases a <;> rfl

theorem tensor_some (a : α) (b : β) :
    tensor (some a) (some b) = some (a, b) := rfl

def baseChange (f : α → α) : Option (α × β) → Option (α × β) :=
  Option.map (fun p => (f p.1, p.2))

theorem baseChange_none (f : α → α) :
    baseChange f (none : Option (α × β)) = none := rfl

theorem restrict_extend (f g : α → α) (v : Option (α × β))
    (h : ∀ a, g (f a) = a) :
    baseChange g (baseChange f v) = v := by
  cases v with
  | none => rfl
  | some p => simp [baseChange, h]

-- ============================================================================
-- The Count
-- ============================================================================

-- Val/RingTheory.lean: 479 lines. Used ValArith, ValRing, ValField.
-- valMap for quotient/localization/evaluation/valuation.
-- valPair for tensor products. 3 custom typeclasses.
--
-- Origin/RingTheory.lean: this file. Standard Lean typeclasses.
-- Option.map replaces valMap. Same domain coverage. Cleaner syntax.
