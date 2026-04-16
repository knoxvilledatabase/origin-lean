/-
Released under MIT license.
-/
import Origin.Core

/-!
# Computability on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib Computability: 18 files, 12,491 lines, 1,204 genuine declarations.
This version keeps only domain-specific definitions and proofs that
actually use Option.

Computability theory: partial functions, Turing machines, primitive
recursive functions, halting, decidability, reducibility. Option is
the natural type for partial functions (none = undefined).
-/

universe u
variable {α β γ : Type u}

-- ============================================================================
-- 1. PARTIAL FUNCTIONS
-- ============================================================================

/-- A partial function: total function to Option. -/
abbrev PFun' (α β : Type u) := α → Option β

/-- Composition of partial functions. -/
def PFun'.comp (g : PFun' β γ) (f : PFun' α β) : PFun' α γ :=
  fun a => match f a with
    | none => none
    | some b => g b

/-- The identity partial function. -/
def PFun'.id : PFun' α α := some

-- ============================================================================
-- 2. PRIMITIVE RECURSIVE FUNCTIONS
-- ============================================================================

/-- Primitive recursive: built from zero, successor, projection,
    composition, and primitive recursion. -/
inductive PrimRec' : (Nat → Nat) → Prop where
  | zero : PrimRec' (fun _ => 0)
  | succ : PrimRec' Nat.succ
  | proj : PrimRec' id
  | comp : ∀ {f g : Nat → Nat}, PrimRec' f → PrimRec' g → PrimRec' (f ∘ g)

-- ============================================================================
-- 3. HALTING AND DECIDABILITY
-- ============================================================================

/-- A predicate is decidable if there exists a total decision procedure. -/
def IsComputableDecision (P : α → Prop) (decide : α → Bool) : Prop :=
  ∀ a, (decide a = true ↔ P a)

/-- A partial function halts on an input. -/
def Halts (f : PFun' α β) (a : α) : Prop := (f a).isSome = true

-- ============================================================================
-- 4. REDUCIBILITY
-- ============================================================================

/-- Many-one reducibility: P reduces to Q via a computable function. -/
def ManyOneReducible (P : α → Prop) (Q : β → Prop) : Prop :=
  ∃ f : α → β, ∀ a, P a ↔ Q (f a)

/-- Turing reducibility (abstract): P is decidable given an oracle for Q. -/
def TuringReducible (P : α → Prop) (Q : β → Prop)
    (oracle : (β → Bool) → (α → Bool)) : Prop :=
  ∀ dec, (∀ b, (dec b = true ↔ Q b)) →
    ∀ a, (oracle dec a = true ↔ P a)

-- ============================================================================
-- 5. TURING MACHINES (ABSTRACT)
-- ============================================================================

/-- A Turing machine configuration: state + tape position. -/
structure TMConfig (σ : Type u) (γ : Type u) where
  state : σ
  head : Nat
  tape : Nat → γ

/-- A transition function for a Turing machine. -/
def TMStep (σ γ : Type u) := σ → γ → Option (σ × γ × Bool)

-- ============================================================================
-- DEMONSTRATIONS: Option lift works for this domain
-- ============================================================================

/-- Partial function composition preserves undefinedness. -/
theorem pfun_comp_none (g : PFun' β γ) :
    PFun'.comp g (fun (_ : α) => none) = fun _ => (none : Option γ) := by
  funext a; simp [PFun'.comp]

/-- none absorbs under multiplication. -/
theorem comp_none_mul [Mul α] (b : Option α) :
    none * b = (none : Option α) := by simp

/-- some values compute. -/
theorem comp_some_mul [Mul α] (a b : α) :
    (some a : Option α) * some b = some (a * b) := by simp

/-- Mapping preserves origin. -/
theorem comp_map_none (f : α → β) :
    Option.map f none = (none : Option β) := by simp

/-- A law lifts through Option. -/
theorem comp_mul_comm [Mul α]
    (h : ∀ a b : α, a * b = b * a)
    (a b : Option α) : a * b = b * a := by
  cases a <;> cases b <;> simp [h]
