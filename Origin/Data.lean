/-
Released under MIT license.
-/
import Origin.Core

/-!
# Data on Option α (Core-based)

GCD, primality, congruence, lists, sets, extended types, multisets,
finsets, matrices, complex numbers, fin types, finsupp, sigma types,
Option lifting demonstrations.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. GCD
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
-- 4. LISTS
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
-- 5. SETS
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

-- ============================================================================
-- 7. MULTISETS (bags — unordered collections with multiplicity)
-- ============================================================================

def optMsetUnion : Option (List α) → Option (List α) → Option (List α)
  | some xs, some ys => some (xs ++ ys)
  | _, _ => none
@[simp] theorem optMsetUnion_none_left (b : Option (List α)) :
    optMsetUnion none b = none := by cases b <;> rfl
@[simp] theorem optMsetUnion_none_right (a : Option (List α)) :
    optMsetUnion a none = none := by cases a <;> rfl
theorem optMsetUnion_comm [DecidableEq α] (xs ys : List α) :
    (optMsetUnion (some xs) (some ys)).map List.length =
    (optMsetUnion (some ys) (some xs)).map List.length := by
  simp [optMsetUnion, List.length_append, Nat.add_comm]
def optMsetCard : Option (List α) → Option Nat
  | some xs => some xs.length
  | none => none
@[simp] theorem optMsetCard_none : optMsetCard (none : Option (List α)) = none := rfl
theorem optMsetCard_union (xs ys : List α) :
    optMsetCard (optMsetUnion (some xs) (some ys)) =
    some (xs.length + ys.length) := by
  simp [optMsetCard, optMsetUnion, List.length_append]

-- ============================================================================
-- 8. FINSETS (finite sets as filtered lists on Option)
-- ============================================================================

def optFinsetMem [DecidableEq α] (a : α) : Option (List α) → Prop
  | some xs => a ∈ xs
  | none => False
def optFinsetInter [DecidableEq α] : Option (List α) → Option (List α) → Option (List α)
  | some xs, some ys => some (xs.filter (· ∈ ys))
  | _, _ => none
@[simp] theorem optFinsetInter_none_left [DecidableEq α] (b : Option (List α)) :
    optFinsetInter none b = none := by cases b <;> rfl
@[simp] theorem optFinsetInter_none_right [DecidableEq α] (a : Option (List α)) :
    optFinsetInter a none = none := by cases a <;> rfl
def optFinsetFilter (p : α → Bool) : Option (List α) → Option (List α)
  | some xs => some (xs.filter p)
  | none => none
@[simp] theorem optFinsetFilter_none (p : α → Bool) :
    optFinsetFilter p (none : Option (List α)) = none := rfl

-- ============================================================================
-- 9. MATRICES (general n×m on Option)
-- ============================================================================

def optMatrix (n m : Nat) (α : Type u) := Option (Fin n → Fin m → α)
def optMatEntry {n m : Nat} (M : optMatrix n m α) (i : Fin n) (j : Fin m) : Option α :=
  M.map (fun f => f i j)
@[simp] theorem optMatEntry_none {n m : Nat} (i : Fin n) (j : Fin m) :
    optMatEntry (none : optMatrix n m α) i j = none := rfl
@[simp] theorem optMatEntry_some {n m : Nat} (f : Fin n → Fin m → α) (i : Fin n) (j : Fin m) :
    optMatEntry (some f : optMatrix n m α) i j = some (f i j) := rfl
def optMatAdd [Add α] {n m : Nat} : optMatrix n m α → optMatrix n m α → optMatrix n m α :=
  liftBin₂ (fun f g i j => f i j + g i j)
@[simp] theorem optMatAdd_none_left [Add α] {n m : Nat} (B : optMatrix n m α) :
    optMatAdd none B = none := by cases B <;> rfl

-- ============================================================================
-- 10. COMPLEX NUMBERS (abstract pair structure on Option)
-- ============================================================================

structure OptComplex (α : Type u) where
  re : Option α
  im : Option α
def optComplexAdd [Add α] (z w : OptComplex α) : OptComplex α :=
  ⟨liftBin₂ (· + ·) z.re w.re, liftBin₂ (· + ·) z.im w.im⟩
theorem optComplexAdd_re_none [Add α] (w : OptComplex α) :
    (optComplexAdd ⟨none, none⟩ w).re = none := by
  simp [optComplexAdd]
def optComplexConj : OptComplex α → OptComplex α
  | ⟨re, im⟩ => ⟨re, im.map id⟩
theorem optComplexConj_re (z : OptComplex α) :
    (optComplexConj z).re = z.re := by simp [optComplexConj]

-- ============================================================================
-- 11. FIN TYPES (finite bounded naturals on Option)
-- ============================================================================

def optFinVal {n : Nat} : Option (Fin n) → Option Nat := Option.map Fin.val
@[simp] theorem optFinVal_none {n : Nat} :
    optFinVal (none : Option (Fin n)) = none := rfl
@[simp] theorem optFinVal_some {n : Nat} (i : Fin n) :
    optFinVal (some i) = some i.val := rfl
theorem optFinVal_bound {n : Nat} (i : Fin n) :
    ∃ k, optFinVal (some i) = some k ∧ k < n :=
  ⟨i.val, rfl, i.isLt⟩

-- ============================================================================
-- 12. FINSUPP (finitely supported functions on Option)
-- ============================================================================

structure OptFinsupp (α β : Type u) where
  toFun : α → Option β
  support : List α
def optFinsuppApply {β : Type u} (f : OptFinsupp α β) (a : α) : Option β := f.toFun a
def optFinsuppMapRange {β γ : Type u} (g : β → γ) (f : OptFinsupp α β) : OptFinsupp α γ :=
  ⟨fun a => (f.toFun a).map g, f.support⟩
theorem optFinsuppMapRange_apply {β γ : Type u} (g : β → γ) (f : OptFinsupp α β) (a : α) :
    (optFinsuppMapRange g f).toFun a = (f.toFun a).map g := rfl

-- ============================================================================
-- 13. SIGMA TYPES (dependent pairs on Option)
-- ============================================================================

def optSigma {β : α → Type u} : Option (Sigma β) → Option α := Option.map Sigma.fst
@[simp] theorem optSigma_none {β : α → Type u} :
    optSigma (none : Option (Sigma β)) = none := rfl
@[simp] theorem optSigma_some {β : α → Type u} (p : Sigma β) :
    optSigma (some p) = some p.fst := rfl
def optSigmaSnd {β : α → Type u} (p : Sigma β) : Option (β p.fst) := some p.snd

-- ============================================================================
-- 14. OPTION LIFTING DEMONSTRATIONS
-- ============================================================================

theorem optMap_comp {γ : Type u} (f : α → β) (g : β → γ) (x : Option α) :
    Option.map g (Option.map f x) = Option.map (g ∘ f) x := by cases x <;> rfl
theorem optMap_id (x : Option α) : Option.map id x = x := by cases x <;> rfl
@[simp] theorem optBind_none (f : α → Option β) : none.bind f = none := rfl
theorem optBind_some (x : Option α) : x.bind some = x := by cases x <;> rfl
theorem liftBin₂_assoc {f : α → α → α}
    (hassoc : ∀ a b c : α, f (f a b) c = f a (f b c))
    (a b c : Option α) :
    liftBin₂ f (liftBin₂ f a b) c = liftBin₂ f a (liftBin₂ f b c) := by
  cases a <;> cases b <;> cases c <;> simp [liftBin₂, hassoc]

-- None absorbs: Core.lean's @[simp] set handles all cases.
