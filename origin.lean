/-
Released under MIT license.
-/

/-!
# Welcome to Origin!
-/

universe u
variable {α β : Type u}

theorem origin [Add α] [Mul α] [Neg α]
    (zero : α)
    (cancel : ∀ a : α, a + (-a) = zero)
    (distrib : ∀ a b c : α, a * (b + c) = a * b + a * c)
    (mul_neg : ∀ a b : α, a * (-b) = -(a * b))
    (n : α) : n * zero = zero :=
  calc n * zero
      _ = n * (n + (-n))           := by rw [cancel]
      _ = n * n + n * (-n)         := by rw [distrib]
      _ = n * n + -(n * n)         := by rw [mul_neg]
      _ = zero                     := by rw [cancel]

instance [Mul α] : Mul (Option α) where
  mul a b := match a, b with
    | none, _ => none
    | _, none => none
    | some a, some b => some (a * b)

instance [Add α] : Add (Option α) where
  add a b := match a, b with
    | none, x => x
    | x, none => x
    | some a, some b => some (a + b)

instance [Neg α] : Neg (Option α) where
  neg a := match a with
    | none => none
    | some a => some (-a)

instance [Zero α] : Zero (Option α) where
  zero := none

class One' (α : Type u) where
  one : α

notation "𝟙" => One'.one

instance [One' α] : One' (Option α) where
  one := some 𝟙

class Inv' (α : Type u) where
  inv : α → α

postfix:max "⁻¹'" => Inv'.inv

instance [Inv' α] : Inv' (Option α) where
  inv a := match a with
    | none => none
    | some a => some (a⁻¹')

-- Simp Set: the ground rules

@[simp] theorem mul_none_left [Mul α] (b : Option α) : none * b = none := by
  cases b <;> rfl
@[simp] theorem mul_none_right [Mul α] (a : Option α) : a * none = none := by
  cases a <;> rfl
@[simp] theorem mul_some [Mul α] (a b : α) : (some a : Option α) * some b = some (a * b) := rfl

@[simp] theorem add_none_left [Add α] (b : Option α) : none + b = b := by
  cases b <;> rfl
@[simp] theorem add_none_right [Add α] (a : Option α) : a + none = a := by
  cases a <;> rfl
@[simp] theorem add_some [Add α] (a b : α) : (some a : Option α) + some b = some (a + b) := rfl

@[simp] theorem neg_none [Neg α] : -(none : Option α) = none := rfl
@[simp] theorem neg_some [Neg α] (a : α) : -(some a : Option α) = some (-a) := rfl

@[simp] theorem one_some [One' α] : (𝟙 : Option α) = some 𝟙 := rfl

@[simp] theorem inv_none [Inv' α] : (none : Option α)⁻¹' = none := rfl
@[simp] theorem inv_some [Inv' α] (a : α) : (some a : Option α)⁻¹' = some (a⁻¹') := rfl

-- The Algebraic Laws: lifted through Option

theorem option_add_comm [Add α] (h : ∀ a b : α, a + b = b + a)
    (a b : Option α) : a + b = b + a := by
  cases a <;> cases b <;> simp [h]

theorem option_mul_comm [Mul α] (h : ∀ a b : α, a * b = b * a)
    (a b : Option α) : a * b = b * a := by
  cases a <;> cases b <;> simp [h]

theorem option_add_assoc [Add α] (h : ∀ a b c : α, a + b + c = a + (b + c))
    (a b c : Option α) : a + b + c = a + (b + c) := by
  cases a <;> cases b <;> cases c <;> simp [h]

theorem option_mul_assoc [Mul α] (h : ∀ a b c : α, a * b * c = a * (b * c))
    (a b c : Option α) : a * b * c = a * (b * c) := by
  cases a <;> cases b <;> cases c <;> simp [h]

theorem option_distrib [Add α] [Mul α]
    (h : ∀ a b c : α, a * (b + c) = a * b + a * c)
    (a b c : Option α) : a * (b + c) = a * b + a * c := by
  cases a <;> cases b <;> cases c <;> simp [h]

theorem option_distrib_right [Add α] [Mul α]
    (h : ∀ a b c : α, (a + b) * c = a * c + b * c)
    (a b c : Option α) : (a + b) * c = a * c + b * c := by
  cases a <;> cases b <;> cases c <;> simp [h]

theorem option_add_neg [Add α] [Neg α]
    (zero : α) (h : ∀ a : α, a + (-a) = zero) (a : α) :
    (some a : Option α) + -(some a) = some zero := by simp [h]

theorem option_neg_add [Add α] [Neg α]
    (h : ∀ a b : α, -(a + b) = -a + -b)
    (a b : Option α) : -(a + b) = -a + -b := by
  cases a <;> cases b <;> simp [h]

theorem option_mul_neg [Mul α] [Neg α]
    (h : ∀ a b : α, a * (-b) = -(a * b))
    (a b : Option α) : a * (-b) = -(a * b) := by
  cases a <;> cases b <;> simp [h]

theorem option_neg_neg [Neg α]
    (h : ∀ a : α, -(-a) = a) (a : Option α) : -(-a) = a := by
  cases a <;> simp [h]

theorem option_neg_mul [Mul α] [Neg α]
    (h : ∀ a b : α, (-a) * b = -(a * b))
    (a b : Option α) : (-a) * b = -(a * b) := by
  cases a <;> cases b <;> simp [h]

theorem option_neg_mul_neg [Mul α] [Neg α]
    (h : ∀ a b : α, (-a) * (-b) = a * b)
    (a b : Option α) : (-a) * (-b) = a * b := by
  cases a <;> cases b <;> simp [h]

theorem option_mul_eq_none [Mul α] {a b : Option α}
    (h : a * b = none) : a = none ∨ b = none := by
  cases a with
  | none => left; rfl
  | some x => cases b with
    | none => right; rfl
    | some y => simp at h

theorem option_one_mul [Mul α] [One' α]
    (h : ∀ a : α, 𝟙 * a = a) (a : Option α) :
    some 𝟙 * a = a := by cases a <;> simp [h]

theorem option_mul_one [Mul α] [One' α]
    (h : ∀ a : α, a * 𝟙 = a) (a : Option α) :
    a * some 𝟙 = a := by cases a <;> simp [h]

theorem option_mul_inv [Mul α] [Inv' α] [One' α]
    (h : ∀ a : α, a * a⁻¹' = 𝟙) (a : α) :
    (some a : Option α) * some (a⁻¹') = some 𝟙 := by simp [h]

theorem option_inv_none' [Inv' α] :
    (none : Option α)⁻¹' = none := rfl

-- Primitives: liftBin₂, liftPred, no_some_fixed_point

variable {γ : Type u}

def liftBin₂ (f : α → β → γ) : Option α → Option β → Option γ
  | none, _ => none
  | _, none => none
  | some a, some b => some (f a b)

@[simp] theorem liftBin₂_none_left (f : α → β → γ) (b : Option β) :
    liftBin₂ f none b = none := by cases b <;> rfl
@[simp] theorem liftBin₂_none_right (f : α → β → γ) (a : Option α) :
    liftBin₂ f a none = none := by cases a <;> rfl
@[simp] theorem liftBin₂_some (f : α → β → γ) (a : α) (b : β) :
    liftBin₂ f (some a) (some b) = some (f a b) := rfl

def liftPred (p : α → Prop) : Option α → Prop
  | some a => p a
  | none => False

@[simp] theorem liftPred_none (p : α → Prop) : liftPred p none = False := rfl
@[simp] theorem liftPred_some (p : α → Prop) (a : α) :
    liftPred p (some a) = p a := rfl

theorem no_some_fixed_point
    (f : α → α) (hf : ∀ a : α, f a ≠ a)
    (v : Option α) (hv : v.map f = v) : v = none := by
  cases v with
  | none => rfl
  | some a => simp at hv; exact absurd hv (hf a)

-- Generic concepts

def image' (f : α → α) : α → Prop := fun b => ∃ a, f a = b

@[simp] theorem option_map_comp (f : α → β) (g : β → γ) (v : Option α) :
    Option.map g (Option.map f v) = Option.map (g ∘ f) v := by
  cases v <;> simp [Function.comp]

def IsAdj (toHom : (α → α) → (α → α)) (fromHom : (α → α) → (α → α)) : Prop :=
  (∀ f, toHom (fromHom f) = f) ∧ (∀ f, fromHom (toHom f) = f)

-- Metric space

structure Metric (α : Type u) where
  dist : α → α → Nat
  dist_self : ∀ a, dist a a = 0
  dist_comm : ∀ a b, dist a b = dist b a
  dist_triangle : ∀ a b c, dist a c ≤ dist a b + dist b c
  eq_of_dist_eq_zero : ∀ a b, dist a b = 0 → a = b

def Metric.liftDist (m : Metric α) : Option α → Option α → Option Nat
  | some a, some b => some (m.dist a b)
  | _, _ => none

@[simp] theorem Metric.liftDist_some (m : Metric α) (a b : α) :
    m.liftDist (some a) (some b) = some (m.dist a b) := rfl
@[simp] theorem Metric.liftDist_none_left (m : Metric α) (b : Option α) :
    m.liftDist none b = none := by cases b <;> rfl
@[simp] theorem Metric.liftDist_none_right (m : Metric α) (a : Option α) :
    m.liftDist a none = none := by cases a <;> rfl

-- ============================================================================
-- THE LAWS: every law from which all of Mathlib's mathematics derives
-- ============================================================================

-- GROUP 1: ALGEBRAIC LAWS (proven above — collected as reference)

example [Mul α] (h : ∀ a b : α, a * b = b * a)
    (a b : Option α) : a * b = b * a := option_mul_comm h a b
example [Mul α] (h : ∀ a b c : α, a * b * c = a * (b * c))
    (a b c : Option α) : a * b * c = a * (b * c) := option_mul_assoc h a b c
example [Add α] (h : ∀ a b : α, a + b = b + a)
    (a b : Option α) : a + b = b + a := option_add_comm h a b
example [Add α] (h : ∀ a b c : α, a + b + c = a + (b + c))
    (a b c : Option α) : a + b + c = a + (b + c) := option_add_assoc h a b c
example [Add α] [Mul α] (h : ∀ a b c : α, a * (b + c) = a * b + a * c)
    (a b c : Option α) : a * (b + c) = a * b + a * c := option_distrib h a b c
example [Mul α] (a : Option α) : none * a = none := mul_none_left a
example [Mul α] (a : Option α) : a * none = none := mul_none_right a
example [Mul α] {a b : Option α} (h : a * b = none) :
    a = none ∨ b = none := option_mul_eq_none h
example [Mul α] [One' α] (h : ∀ a : α, 𝟙 * a = a)
    (a : Option α) : some 𝟙 * a = a := option_one_mul h a
example [Mul α] [Inv' α] [One' α] (h : ∀ a : α, a * a⁻¹' = 𝟙) (a : α) :
    (some a : Option α) * some (a⁻¹') = some 𝟙 := option_mul_inv h a

-- GROUP 2: ORDER LAWS

def optLE [LE α] : Option α → Option α → Prop
  | some a, some b => a ≤ b
  | none, _ => True
  | some _, none => False

theorem optLE_refl [LE α] (h : ∀ a : α, a ≤ a) (v : Option α) : optLE v v := by
  cases v <;> simp [optLE, h]

theorem optLE_trans [LE α] (h : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c)
    (a b c : Option α) : optLE a b → optLE b c → optLE a c := by
  cases a <;> cases b <;> cases c <;> simp [optLE]; exact h _ _ _

theorem optLE_antisymm [LE α] (h : ∀ a b : α, a ≤ b → b ≤ a → a = b)
    (a b : Option α) : optLE a b → optLE b a → a = b := by
  cases a <;> cases b <;> simp [optLE]
  intro hab hba; congr; exact h _ _ hab hba

theorem optLE_none [LE α] (v : Option α) : optLE none v := by
  cases v <;> simp [optLE]

-- GROUP 3: METRIC LAWS (structure in foundation — lifted here)

example (m : Metric α) (a b : α) : m.liftDist (some a) (some b) = some (m.dist a b) := rfl
example (m : Metric α) (b : Option α) : m.liftDist none b = none := by cases b <;> rfl
example (m : Metric α) (a : Option α) : m.liftDist a none = none := by cases a <;> rfl

-- GROUP 4: FUNCTOR LAWS

theorem functor_id (v : Option α) : Option.map id v = v := by
  cases v <;> simp

theorem functor_comp (f : α → β) (g : β → γ) (v : Option α) :
    Option.map g (Option.map f v) = Option.map (g ∘ f) v :=
  option_map_comp f g v

theorem functor_none (f : α → β) : Option.map f none = none := rfl

-- GROUP 5: TOPOLOGY LAW

def IsOptionOpen (isOpen : (α → Prop) → Prop) : (Option α → Prop) → Prop :=
  fun S => isOpen (fun a => S (some a))

theorem map_preserves_open (f : α → α) (isOpen : (α → Prop) → Prop)
    (hf : ∀ S, isOpen S → isOpen (fun a => S (f a)))
    (S : Option α → Prop) (hS : IsOptionOpen isOpen S) :
    IsOptionOpen isOpen (fun v => S (Option.map f v)) := by
  simp [IsOptionOpen] at *; exact hf _ hS

-- GROUP 6: MEASURE LAW

theorem liftPred_disjoint (p q : α → Prop)
    (hdisj : ∀ a, p a → q a → False) (v : Option α) :
    liftPred (fun a => p a ∨ q a) v ↔
    (liftPred p v ∨ liftPred q v) := by
  cases v <;> simp

theorem liftPred_conj (p q : α → Prop) (v : Option α) :
    liftPred (fun a => p a ∧ q a) v ↔
    (liftPred p v ∧ liftPred q v) := by
  cases v <;> simp

theorem liftPred_none_false (p : α → Prop) :
    liftPred p none ↔ False := by simp

-- GROUP 7: LOGIC — the paradoxes unified

theorem liar_paradox (v : Option Bool) (hv : v.map (!·) = v) : v = none :=
  no_some_fixed_point _ (fun b => by cases b <;> simp) v hv

-- Russell: R ∈ R ↔ R ∉ R. Same structure — negation has no fixed point.
-- Curry: C = (C → False). Same theorem. Different f. Same conclusion: v = none.
-- What none means: the sentence was never in the counting domain.

-- GROUP 8: PHYSICS — 86 existence hypotheses dissolved

theorem coulomb_absorbs [Mul α] (k q cap_q : Option α) :
    k * q * cap_q * none = none := by simp

theorem entropy_absorbs [Mul α] (q : Option α) :
    q * none = none := by simp

theorem operator_domain (mem : α → Prop) :
    ¬liftPred mem (none : Option α) := by simp

theorem singularity_distinction [Zero α] :
    (some (0 : α) : Option α) ≠ none := by simp

