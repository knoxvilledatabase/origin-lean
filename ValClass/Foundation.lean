/-
Released under MIT license.
-/

/-!
# Val α: Level 0 — The Type

Three constructors. Sort dispatch via @[simp]. The universal infrastructure
that every level and every domain uses. No classes. No operations. Just the type.
-/

universe u

-- ============================================================================
-- The Type
-- ============================================================================

inductive Val (α : Type u) where
  | origin : Val α
  | container : α → Val α
  | contents : α → Val α
deriving DecidableEq, Repr

namespace Val

variable {α : Type u}

-- ============================================================================
-- valMap: Sort-Preserving Maps (the universal functor)
-- ============================================================================

def valMap {β : Type u} (f : α → β) : Val α → Val β
  | origin => origin
  | container a => container (f a)
  | contents a => contents (f a)

@[simp] theorem valMap_origin {β : Type u} (f : α → β) :
    valMap f (origin : Val α) = origin := rfl
@[simp] theorem valMap_container {β : Type u} (f : α → β) (a : α) :
    valMap f (container a) = container (f a) := rfl
@[simp] theorem valMap_contents {β : Type u} (f : α → β) (a : α) :
    valMap f (contents a) = contents (f a) := rfl

theorem valMap_id : valMap (id : α → α) = id := by
  funext x; cases x <;> rfl

theorem valMap_comp {β γ : Type u} (f : α → β) (g : β → γ) :
    valMap (g ∘ f) = valMap g ∘ valMap f := by
  funext x; cases x <;> rfl

theorem valMap_injective {β : Type u} {f : α → β}
    (hf : ∀ a b, f a = f b → a = b) :
    ∀ x y : Val α, valMap f x = valMap f y → x = y := by
  intro x y h
  cases x <;> cases y <;> simp [valMap] at h ⊢ <;> exact hf _ _ h

theorem valMap_ext {β : Type u} {f g : α → β} (h : ∀ a, f a = g a)
    (x : Val α) : valMap f x = valMap g x := by
  cases x <;> simp [valMap, h]

-- ============================================================================
-- valPair: Cross-Type Pairing
-- ============================================================================

def valPair {β : Type u} : Val α → Val β → Val (α × β)
  | origin, _                => origin
  | _, origin                => origin
  | container a, container b => container (a, b)
  | container a, contents b  => container (a, b)
  | contents a, container b  => container (a, b)
  | contents a, contents b   => contents (a, b)

@[simp] theorem valPair_origin_left {β : Type u} (b : Val β) :
    valPair (origin : Val α) b = origin := by cases b <;> rfl
@[simp] theorem valPair_origin_right {β : Type u} (a : Val α) :
    valPair a (origin : Val β) = origin := by cases a <;> rfl
@[simp] theorem valPair_contents_contents {β : Type u} (a : α) (b : β) :
    valPair (contents a) (contents b) = contents (a, b) := rfl
@[simp] theorem valPair_container_container {β : Type u} (a : α) (b : β) :
    valPair (container a) (container b) = container (a, b) := rfl
@[simp] theorem valPair_container_contents {β : Type u} (a : α) (b : β) :
    valPair (container a) (contents b) = container (a, b) := rfl
@[simp] theorem valPair_contents_container {β : Type u} (a : α) (b : β) :
    valPair (contents a) (container b) = container (a, b) := rfl

-- ============================================================================
-- Contents Existence (eliminates trivial ⟨_, rfl⟩ patterns)
-- ============================================================================

theorem contents_exists (a : α) : ∃ r, (contents a : Val α) = contents r := ⟨a, rfl⟩

-- ============================================================================
-- Sort Predicates
-- ============================================================================

def isOrigin : Val α → Prop
  | origin => True
  | _ => False

def isContainer : Val α → Prop
  | container _ => True
  | _ => False

def isContents : Val α → Prop
  | contents _ => True
  | _ => False

@[simp] theorem isOrigin_origin : isOrigin (origin : Val α) = True := rfl
@[simp] theorem isOrigin_container (a : α) : isOrigin (container a : Val α) = False := rfl
@[simp] theorem isOrigin_contents (a : α) : isOrigin (contents a : Val α) = False := rfl
@[simp] theorem isContainer_origin : isContainer (origin : Val α) = False := rfl
@[simp] theorem isContainer_container (a : α) : isContainer (container a : Val α) = True := rfl
@[simp] theorem isContainer_contents (a : α) : isContainer (contents a : Val α) = False := rfl
@[simp] theorem isContents_origin : isContents (origin : Val α) = False := rfl
@[simp] theorem isContents_container (a : α) : isContents (container a : Val α) = False := rfl
@[simp] theorem isContents_contents (a : α) : isContents (contents a : Val α) = True := rfl

-- ============================================================================
-- Sort Disjointness
-- ============================================================================

@[simp] theorem origin_ne_container (a : α) : (origin : Val α) ≠ container a := by intro h; cases h
@[simp] theorem origin_ne_contents (a : α) : (origin : Val α) ≠ contents a := by intro h; cases h
@[simp] theorem container_ne_origin (a : α) : (container a : Val α) ≠ origin := by intro h; cases h
@[simp] theorem container_ne_contents (a b : α) : (container a : Val α) ≠ contents b := by intro h; cases h
@[simp] theorem contents_ne_origin (a : α) : (contents a : Val α) ≠ origin := by intro h; cases h
@[simp] theorem contents_ne_container (a b : α) : (contents a : Val α) ≠ container b := by intro h; cases h

-- ============================================================================
-- Injectivity
-- ============================================================================

@[simp] theorem contents_inj (a b : α) :
    (contents a : Val α) = contents b ↔ a = b := by
  constructor
  · intro h; cases h; rfl
  · intro h; rw [h]

@[simp] theorem container_inj (a b : α) :
    (container a : Val α) = container b ↔ a = b := by
  constructor
  · intro h; cases h; rfl
  · intro h; rw [h]

-- ============================================================================
-- Contents Congruence
-- ============================================================================

@[simp] theorem contents_congr {a b : α} (h : a = b) :
    (contents a : Val α) = contents b := by rw [h]

@[simp] theorem container_congr {a b : α} (h : a = b) :
    (container a : Val α) = container b := by rw [h]

-- ============================================================================
-- Sort Trichotomy
-- ============================================================================

theorem sort_trichotomy (x : Val α) :
    x = origin ∨ (∃ a, x = container a) ∨ (∃ a, x = contents a) := by
  cases x with
  | origin => left; rfl
  | container a => right; left; exact ⟨a, rfl⟩
  | contents a => right; right; exact ⟨a, rfl⟩

end Val
