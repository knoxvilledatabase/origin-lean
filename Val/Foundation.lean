/-
Released under MIT license.
-/

/-!
# Val α: The Foundation

Three constructors. Four rules. The app that every domain extends.

- `origin` — the ground. Nothing to retrieve. Absorbs everything.
- `container` — the hand. Carries the last known value.
- `contents` — the apple. Safe territory. Arithmetic lives here.

Every operation dispatches on the sort first, then computes within contents.
Every simp lemma is tagged. Every constructor combination is covered.
A domain file imports this and writes `by simp`. That's the goal.
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
-- Operations: explicit function parameters, zero typeclasses
-- ============================================================================

def mul (f : α → α → α) : Val α → Val α → Val α
  | origin, _                  => origin
  | _, origin                  => origin
  | container a, container b   => container (f a b)
  | container a, contents b    => container (f a b)
  | contents a, container b    => container (f a b)
  | contents a, contents b     => contents (f a b)

def add (f : α → α → α) : Val α → Val α → Val α
  | origin, _                  => origin
  | _, origin                  => origin
  | container a, container b   => container (f a b)
  | container a, contents b    => container (f a b)
  | contents a, container b    => container (f a b)
  | contents a, contents b     => contents (f a b)

def neg (f : α → α) : Val α → Val α
  | origin       => origin
  | container a  => container (f a)
  | contents a   => contents (f a)

def inv (f : α → α) : Val α → Val α
  | origin       => origin
  | container a  => container (f a)
  | contents a   => contents (f a)

def fdiv (mulF : α → α → α) (invF : α → α) (a b : Val α) : Val α :=
  mul mulF a (inv invF b)

def project : Val α → Option α
  | origin       => none
  | container a  => some a
  | contents a   => some a

-- ============================================================================
-- Simp Set: all constructor combinations for mul
-- ============================================================================

@[simp] theorem mul_origin_left (f : α → α → α) (a : Val α) :
    mul f origin a = origin := by cases a <;> rfl

@[simp] theorem mul_origin_right (f : α → α → α) (a : Val α) :
    mul f a origin = origin := by cases a <;> rfl

@[simp] theorem mul_contents_contents (f : α → α → α) (a b : α) :
    mul f (contents a) (contents b) = contents (f a b) := rfl

@[simp] theorem mul_container_container (f : α → α → α) (a b : α) :
    mul f (container a) (container b) = container (f a b) := rfl

@[simp] theorem mul_container_contents (f : α → α → α) (a b : α) :
    mul f (container a) (contents b) = container (f a b) := rfl

@[simp] theorem mul_contents_container (f : α → α → α) (a b : α) :
    mul f (contents a) (container b) = container (f a b) := rfl

-- ============================================================================
-- Simp Set: all constructor combinations for add
-- ============================================================================

@[simp] theorem add_origin_left (f : α → α → α) (a : Val α) :
    add f origin a = origin := by cases a <;> rfl

@[simp] theorem add_origin_right (f : α → α → α) (a : Val α) :
    add f a origin = origin := by cases a <;> rfl

@[simp] theorem add_contents_contents (f : α → α → α) (a b : α) :
    add f (contents a) (contents b) = contents (f a b) := rfl

@[simp] theorem add_container_container (f : α → α → α) (a b : α) :
    add f (container a) (container b) = container (f a b) := rfl

@[simp] theorem add_container_contents (f : α → α → α) (a b : α) :
    add f (container a) (contents b) = container (f a b) := rfl

@[simp] theorem add_contents_container (f : α → α → α) (a b : α) :
    add f (contents a) (container b) = container (f a b) := rfl

-- ============================================================================
-- Simp Set: neg and inv
-- ============================================================================

@[simp] theorem neg_origin (f : α → α) : neg f (origin : Val α) = origin := rfl
@[simp] theorem neg_container (f : α → α) (a : α) : neg f (container a) = container (f a) := rfl
@[simp] theorem neg_contents (f : α → α) (a : α) : neg f (contents a) = contents (f a) := rfl

@[simp] theorem inv_origin (f : α → α) : inv f (origin : Val α) = origin := rfl
@[simp] theorem inv_container (f : α → α) (a : α) : inv f (container a) = container (f a) := rfl
@[simp] theorem inv_contents (f : α → α) (a : α) : inv f (contents a) = contents (f a) := rfl

-- ============================================================================
-- Simp Set: project
-- ============================================================================

@[simp] theorem project_origin : project (origin : Val α) = none := rfl
@[simp] theorem project_container (a : α) : project (container a) = some a := rfl
@[simp] theorem project_contents (a : α) : project (contents a) = some a := rfl

-- ============================================================================
-- Sort-Preserving Maps
-- ============================================================================

/-- Sort-preserving map: origin → origin, container → container, contents → contents.
    The canonical unary lift. Every domain's "apply f to the value" is this. -/
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

-- ============================================================================
-- valMap: Structural Properties
-- ============================================================================

/-- valMap preserves injectivity. If f is injective, valMap f is injective. -/
theorem valMap_injective {β : Type u} {f : α → β}
    (hf : ∀ a b, f a = f b → a = b) :
    ∀ x y : Val α, valMap f x = valMap f y → x = y := by
  intro x y h
  cases x <;> cases y <;> simp [valMap] at h ⊢ <;> exact hf _ _ h

/-- valMap preserves surjectivity. If f is surjective, valMap f is surjective. -/
theorem valMap_surjective {β : Type u} {f : α → β}
    (hf : ∀ b, ∃ a, f a = b) :
    ∀ y : Val β, ∃ x : Val α, valMap f x = y := by
  intro y; cases y with
  | origin => exact ⟨origin, rfl⟩
  | container b => obtain ⟨a, ha⟩ := hf b; exact ⟨container a, by simp [ha]⟩
  | contents b => obtain ⟨a, ha⟩ := hf b; exact ⟨contents a, by simp [ha]⟩

/-- valMap id = id -/
theorem valMap_id : valMap (id : α → α) = id := by
  funext x; cases x <;> rfl

/-- valMap (g ∘ f) = valMap g ∘ valMap f -/
theorem valMap_comp {β γ : Type u} (f : α → β) (g : β → γ) :
    valMap (g ∘ f) = valMap g ∘ valMap f := by
  funext x; cases x <;> rfl

/-- valMap extensionality: pointwise equal functions give equal valMaps. -/
theorem valMap_ext {β : Type u} {f g : α → β} (h : ∀ a, f a = g a)
    (x : Val α) : valMap f x = valMap g x := by
  cases x <;> simp [valMap, h]

/-- Contents congruence: equal α values give equal contents. -/
@[simp] theorem contents_congr {a b : α} (h : a = b) :
    (contents a : Val α) = contents b := by rw [h]

/-- Container congruence: equal α values give equal containers. -/
@[simp] theorem container_congr {a b : α} (h : a = b) :
    (container a : Val α) = container b := by rw [h]

-- ============================================================================
-- Cross-Type Pairing
-- ============================================================================

/-- Sort-preserving binary pairing across types. The canonical binary lift for
    cross-type operations. Same-type binary ops should use mul/add instead. -/
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
-- Contents existence (trivial but used 60+ times across domains)
-- ============================================================================

theorem contents_exists (a : α) : ∃ r, (contents a : Val α) = contents r := ⟨a, rfl⟩

-- ============================================================================
-- Sort predicates
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
-- Sort disjointness
-- ============================================================================

@[simp] theorem origin_ne_container (a : α) : (origin : Val α) ≠ container a := by intro h; cases h
@[simp] theorem origin_ne_contents (a : α) : (origin : Val α) ≠ contents a := by intro h; cases h
@[simp] theorem container_ne_origin (a : α) : (container a : Val α) ≠ origin := by intro h; cases h
@[simp] theorem container_ne_contents (a b : α) : (container a : Val α) ≠ contents b := by intro h; cases h
@[simp] theorem contents_ne_origin (a : α) : (contents a : Val α) ≠ origin := by intro h; cases h
@[simp] theorem contents_ne_container (a b : α) : (contents a : Val α) ≠ container b := by intro h; cases h

-- ============================================================================
-- Sort trichotomy
-- ============================================================================

theorem sort_trichotomy (x : Val α) :
    x = origin ∨ (∃ a, x = container a) ∨ (∃ a, x = contents a) := by
  cases x with
  | origin => left; rfl
  | container a => right; left; exact ⟨a, rfl⟩
  | contents a => right; right; exact ⟨a, rfl⟩

-- ============================================================================
-- Contents closure: contents never produce origin
-- ============================================================================

theorem mul_contents_ne_origin (f : α → α → α) (a b : α) :
    mul f (contents a) (contents b) ≠ origin := by simp

theorem add_contents_ne_origin (f : α → α → α) (a b : α) :
    add f (contents a) (contents b) ≠ origin := by simp

-- ============================================================================
-- Injectivity
-- ============================================================================

theorem contents_injective (a b : α) (h : (contents a : Val α) = contents b) :
    a = b := by cases h; rfl

@[simp] theorem contents_inj (a b : α) :
    (contents a : Val α) = contents b ↔ a = b := by
  constructor
  · exact contents_injective a b
  · intro h; rw [h]

theorem container_injective (a b : α) (h : (container a : Val α) = container b) :
    a = b := by cases h; rfl

@[simp] theorem container_inj (a b : α) :
    (container a : Val α) = container b ↔ a = b := by
  constructor
  · exact container_injective a b
  · intro h; rw [h]

end Val
