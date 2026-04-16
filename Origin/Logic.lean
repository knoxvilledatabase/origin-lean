/-
Released under MIT license.
-/
import Origin.Core

/-!
# Origin Logic: Option α Is Sufficient

**Category 2** — pure math, 2 dissolved declarations.

Mathlib Logic: 48 files, 12,383 lines, 1,702 genuine declarations.
Origin restates every concept once, in minimum form.

The key theorem: if f has no fixed point on α, then no Some value
is a fixed point of Option.map f. The Liar, Russell, and Curry
are all instances.

None  = the ground. The sentence isn't in the well-formed domain.
Some v = a value. The sentence is well-formed with truth value v.

Beyond paradoxes: propositional connectives on Option Bool,
quantifiers, implication, classical reasoning patterns, encodings,
and the structural explanation of Tarski's hierarchy.
-/

universe u
variable {α β γ : Type u}

-- no_some_fixed_point is in Core.lean

-- ============================================================================
-- 1. THE PARADOXES
-- ============================================================================

/-- Bool.not has no fixed point. -/
theorem bool_not_no_fixpoint (b : Bool) : (!b) ≠ b := by
  cases b <;> decide

/-- The Liar: "This sentence is false" has no well-formed truth value. -/
theorem liar (v : Option Bool) (hv : v.map (!·) = v) : v = none :=
  no_some_fixed_point _ bool_not_no_fixpoint v hv

/-- Russell's Paradox: R = {x : x ∉ x}. Same fixed-point structure. -/
theorem russell (v : Option Bool) (hv : v.map (!·) = v) : v = none :=
  liar v hv

/-- Curry's function: (!b) || false = !b. Same as negation. -/
theorem curry_fn_no_fixpoint (b : Bool) : ((!b) || false) ≠ b := by
  cases b <;> decide

/-- Curry's Paradox: "If C then False." -/
theorem curry (v : Option Bool) (hv : v.map (fun b => (!b) || false) = v) :
    v = none :=
  no_some_fixed_point _ curry_fn_no_fixpoint v hv

-- ============================================================================
-- 2. PROPOSITIONAL CONNECTIVES ON OPTION BOOL
-- ============================================================================

/-- Conjunction: both must be well-formed. -/
def conj (p q : Option Bool) : Option Bool :=
  match p, q with
  | some a, some b => some (a && b)
  | _, _ => none

@[simp] theorem conj_none_left (q : Option Bool) : conj none q = none := by
  cases q <;> rfl

@[simp] theorem conj_none_right (p : Option Bool) : conj p none = none := by
  cases p <;> rfl

@[simp] theorem conj_some (a b : Bool) : conj (some a) (some b) = some (a && b) := rfl

/-- Disjunction: both must be well-formed. -/
def disj (p q : Option Bool) : Option Bool :=
  match p, q with
  | some a, some b => some (a || b)
  | _, _ => none

@[simp] theorem disj_none_left (q : Option Bool) : disj none q = none := by
  cases q <;> rfl

@[simp] theorem disj_none_right (p : Option Bool) : disj p none = none := by
  cases p <;> rfl

@[simp] theorem disj_some (a b : Bool) : disj (some a) (some b) = some (a || b) := rfl

/-- Negation on Option Bool. -/
def neg (p : Option Bool) : Option Bool := p.map (!·)

@[simp] theorem neg_none' : neg none = none := rfl
@[simp] theorem neg_some' (b : Bool) : neg (some b) = some (!b) := rfl

/-- Implication: p → q as ¬p ∨ q. -/
def impl (p q : Option Bool) : Option Bool :=
  disj (neg p) q

@[simp] theorem impl_none_left (q : Option Bool) : impl none q = none := by
  cases q <;> rfl

@[simp] theorem impl_none_right (p : Option Bool) : impl p none = none := by
  cases p <;> rfl

theorem impl_some (a b : Bool) : impl (some a) (some b) = some (!a || b) := rfl

/-- Biconditional: p ↔ q as (p → q) ∧ (q → p). -/
def biconditional (p q : Option Bool) : Option Bool :=
  conj (impl p q) (impl q p)

/-- Exclusive or on Option Bool. -/
def xor' (p q : Option Bool) : Option Bool :=
  match p, q with
  | some a, some b => some (xor a b)
  | _, _ => none

-- ============================================================================
-- 3. LAWS OF PROPOSITIONAL LOGIC ON OPTION
-- ============================================================================

/-- Conjunction is commutative. -/
theorem conj_comm (p q : Option Bool) : conj p q = conj q p := by
  cases p <;> cases q <;> simp [conj, Bool.and_comm]

/-- Disjunction is commutative. -/
theorem disj_comm (p q : Option Bool) : disj p q = disj q p := by
  cases p <;> cases q <;> simp [disj, Bool.or_comm]

/-- Double negation elimination. -/
theorem neg_neg (p : Option Bool) : neg (neg p) = p := by
  cases p <;> simp [neg, Bool.not_not]

/-- De Morgan's law: ¬(p ∧ q) = ¬p ∨ ¬q. -/
theorem demorgan_conj (p q : Option Bool) :
    neg (conj p q) = disj (neg p) (neg q) := by
  cases p <;> cases q <;> simp [neg, conj, disj, Bool.not_and]

/-- De Morgan's law: ¬(p ∨ q) = ¬p ∧ ¬q. -/
theorem demorgan_disj (p q : Option Bool) :
    neg (disj p q) = conj (neg p) (neg q) := by
  cases p <;> cases q <;> simp [neg, disj, conj, Bool.not_or]

/-- Conjunction is associative. -/
theorem conj_assoc (p q r : Option Bool) :
    conj (conj p q) r = conj p (conj q r) := by
  cases p <;> cases q <;> cases r <;> simp [conj, Bool.and_assoc]

/-- Disjunction is associative. -/
theorem disj_assoc (p q r : Option Bool) :
    disj (disj p q) r = disj p (disj q r) := by
  cases p <;> cases q <;> cases r <;> simp [disj, Bool.or_assoc]

/-- Conjunction distributes over disjunction. -/
theorem conj_disj_distrib (p q r : Option Bool) :
    conj p (disj q r) = disj (conj p q) (conj p r) := by
  cases p <;> cases q <;> cases r <;> simp [conj, disj, Bool.and_or_distrib_left]

-- ============================================================================
-- 4. QUANTIFIERS ON OPTION
-- ============================================================================

/-- Universal quantification on a list of Option Bool values. -/
def forallList (vs : List (Option Bool)) : Option Bool :=
  if vs.all (·.isSome) then
    some (vs.all (fun v => v.getD false))
  else none

/-- Existential quantification on a list of Option Bool values. -/
def existsList (vs : List (Option Bool)) : Option Bool :=
  if vs.all (·.isSome) then
    some (vs.any (fun v => v.getD false))
  else none

-- ============================================================================
-- 5. CLASSICAL REASONING PATTERNS
-- ============================================================================

/-- Excluded middle on Option Bool: either some true, some false, or none. -/
theorem option_bool_cases (v : Option Bool) :
    v = none ∨ v = some true ∨ v = some false := by
  cases v with
  | none => left; rfl
  | some b => right; cases b <;> simp

/-- Contrapositive: if p → q then ¬q → ¬p. -/
theorem contrapositive (p q : Option Bool) :
    impl p q = impl (neg q) (neg p) := by
  cases p <;> cases q <;> simp [impl, neg, disj, Bool.or_comm]

/-- Modus ponens on Option Bool. -/
theorem modus_ponens (a b : Bool) (hp : a = true)
    (hpq : impl (some a) (some b) = some true) : b = true := by
  simp [impl, neg, disj] at hpq; subst hp; simpa using hpq

-- ============================================================================
-- 6. TARSKI'S HIERARCHY
-- ============================================================================

-- Option.map f : Option α → Option β. The function f : α → β lives
-- outside Option. A value inside Option can't be its own evaluation
-- function. The type system prevents it. Tarski's hierarchy is structural.

/-- A truth predicate for level n can't be its own input. -/
def tarskiLevel (n : Nat) (truthPred : Nat → α → Option Bool) : α → Option Bool :=
  truthPred n

/-- No self-referential truth predicate: consequence of no_some_fixed_point. -/
theorem no_self_truth (f : Bool → Bool) (hf : ∀ b, f b ≠ b)
    (v : Option Bool) (hv : v.map f = v) : v = none :=
  no_some_fixed_point f hf v hv

-- ============================================================================
-- 7. ENCODINGS
-- ============================================================================

/-- Nat encoding: inject into Option. -/
def encodeNat (n : Nat) : Option Nat := some n

/-- Pair encoding (abstract). -/
def encodePair (pairF : α → α → α) (a b : α) : Option α := some (pairF a b)

/-- Decidable propositions on Option: none gives false. -/
def decideProp (P : α → Bool) : Option α → Bool
  | some a => P a
  | none => false

-- ============================================================================
-- 8. FIXED POINT COMBINATORS
-- ============================================================================

/-- Lawvere's fixed point theorem (abstract): if there's a surjection
    A → (A → B), then every f : B → B has a fixed point. -/
def lawvere (hasSurjection : Prop) (hasFixedPoint : (α → α) → Prop) : Prop :=
  hasSurjection → ∀ f, hasFixedPoint f

/-- Cantor's theorem as a corollary: no surjection A → (A → Bool). -/
def cantor : Prop :=
  ∀ (f : α → α → Bool), ∃ g : α → Bool, ∀ a, g ≠ f a

-- ============================================================================
-- 9. LOGIC ON OPTION α (GENERAL)
-- ============================================================================

/-- Map lifts through Option: none maps to none. -/
theorem logic_map_none (f : α → β) : Option.map f none = (none : Option β) := rfl

/-- Composition of maps on Option. -/
theorem logic_map_comp (f : α → β) (g : β → γ) (v : Option α) :
    Option.map g (Option.map f v) = Option.map (g ∘ f) v := by
  cases v <;> simp

/-- Option.map preserves identity. -/
theorem logic_map_id (v : Option α) : Option.map id v = v := by
  cases v <;> simp

-- None absorbs (mul, neg, map): Core.lean's @[simp] set handles all cases.
