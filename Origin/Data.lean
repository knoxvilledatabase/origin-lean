/-
Released under MIT license.
-/
import Origin.Core

/-!
# Data on Option α (Core-based)

Val/Data.lean: 1121 lines. Number tower, lists, multisets, sets, finsets,
matrix, complex, extended number types, fin/fintype, finsupp.

This version keeps only domain-specific definitions and proofs that
actually use Option.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. GCD (binary lift — like liftBin₂)
-- ============================================================================

def optGcd (gcdF : α → α → α) : Option α → Option α → Option α
  | some a, some b => some (gcdF a b)
  | _, _ => none

@[simp] theorem optGcd_none_left (gcdF : α → α → α) (b : Option α) :
    optGcd gcdF none b = none := by cases b <;> rfl

@[simp] theorem optGcd_none_right (gcdF : α → α → α) (a : Option α) :
    optGcd gcdF a none = none := by cases a <;> rfl

@[simp] theorem optGcd_some (gcdF : α → α → α) (a b : α) :
    optGcd gcdF (some a) (some b) = some (gcdF a b) := rfl

theorem optGcd_comm (gcdF : α → α → α)
    (h : ∀ a b : α, gcdF a b = gcdF b a) (a b : Option α) :
    optGcd gcdF a b = optGcd gcdF b a := by
  cases a <;> cases b <;> simp [optGcd, h]

-- ============================================================================
-- 2. PRIMALITY
-- ============================================================================

def optIsPrime (primeP : α → Prop) : Option α → Prop
  | some a => primeP a
  | none => False

@[simp] theorem optIsPrime_none (primeP : α → Prop) :
    optIsPrime primeP (none : Option α) = False := rfl

-- ============================================================================
-- 3. CONGRUENCE
-- ============================================================================

def optCong (modF : α → α → α) (a b n : α) : Prop := modF a n = modF b n

theorem optCong_refl (modF : α → α → α) (a n : α) : optCong modF a a n := rfl

theorem optCong_symm (modF : α → α → α) (a b n : α)
    (h : optCong modF a b n) : optCong modF b a n := h.symm

theorem optCong_trans (modF : α → α → α) (a b c n : α)
    (hab : optCong modF a b n) (hbc : optCong modF b c n) :
    optCong modF a c n := hab.trans hbc

-- ============================================================================
-- 4. LISTS (binary lift for append, Option.map for the rest)
-- ============================================================================

variable {β : Type u}

def optAppend : Option (List α) → Option (List α) → Option (List α)
  | some xs, some ys => some (xs ++ ys)
  | _, _ => none

@[simp] theorem optAppend_none_left (ys : Option (List α)) :
    optAppend none ys = none := by cases ys <;> rfl

@[simp] theorem optAppend_none_right (xs : Option (List α)) :
    optAppend xs none = none := by cases xs <;> rfl

@[simp] theorem optAppend_some (xs ys : List α) :
    optAppend (some xs) (some ys) = some (xs ++ ys) := rfl

theorem optAppend_assoc (xs ys zs : List α) :
    optAppend (optAppend (some xs) (some ys)) (some zs) =
    optAppend (some xs) (optAppend (some ys) (some zs)) := by
  simp [List.append_assoc]

theorem list_reverse_involutive (xs : List α) :
    Option.map List.reverse (Option.map List.reverse (some xs)) = some xs := by
  simp [List.reverse_reverse]

theorem listMap_append (f : α → β) (xs ys : List α) :
    Option.map (List.map f) (optAppend (some xs) (some ys)) =
    optAppend (Option.map (List.map f) (some xs)) (Option.map (List.map f) (some ys)) := by
  simp [optAppend, List.map_append]

-- ============================================================================
-- 5. SETS: predicates
-- ============================================================================

def optInjective (f : α → α) : Prop := ∀ a b, f a = f b → a = b
def optSurjective (f : α → α) : Prop := ∀ b, ∃ a, f a = b
def optBijective (f : α → α) : Prop := optInjective f ∧ optSurjective f

theorem bijective_comp (f g : α → α)
    (hf : optBijective f) (hg : optBijective g) :
    optBijective (f ∘ g) := by
  constructor
  · intro a b h; exact hg.1 _ _ (hf.1 _ _ h)
  · intro c; obtain ⟨b, hb⟩ := hf.2 c; obtain ⟨a, ha⟩ := hg.2 b
    exact ⟨a, by simp [Function.comp, ha, hb]⟩

-- ============================================================================
-- 6. EXTENDED NUMBER TYPES
-- ============================================================================

def optIsTop (topP : α → Prop) : Option α → Prop
  | some a => topP a
  | none => False

def optIsBot (botP : α → Prop) : Option α → Prop
  | some a => botP a
  | none => False

-- None absorbs (mul, neg, map): Core.lean's @[simp] set handles all cases.
-- Option.map replaces optCons, optLength, optReverse, optListMap, optPermSign.
