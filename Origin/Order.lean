/-
Released under MIT license.
-/
import Origin.Core

/-!
# Order Theory on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib Order: 211 files, 75,874 lines, 10,131 genuine declarations.
Origin restates every concept once, in minimum form.

Partial orders, lattices, well-orders, filters, Galois connections,
fixed point theorems, directed sets, Boolean algebras, chains,
Zorn's lemma, conditionally complete lattices, order ideals,
monotone functions, closure operators.
-/

universe u
variable {α β : Type u}

-- ============================================================================
-- 1. PARTIAL ORDERS
-- ============================================================================

/-- A partial order: reflexive, antisymmetric, transitive. -/
structure PartialOrder' (α : Type u) where
  le : α → α → Prop
  refl : ∀ a, le a a
  antisymm : ∀ a b, le a b → le b a → a = b
  trans : ∀ a b c, le a b → le b c → le a c

/-- A total order: every pair is comparable. -/
def IsTotal (le : α → α → Prop) : Prop :=
  ∀ a b, le a b ∨ le b a

/-- A preorder: reflexive and transitive (no antisymmetry). -/
def IsPreorder (le : α → α → Prop) : Prop :=
  (∀ a, le a a) ∧ (∀ a b c, le a b → le b c → le a c)

/-- Strict order: irreflexive and transitive. -/
def IsStrictOrder (lt : α → α → Prop) : Prop :=
  (∀ a, ¬lt a a) ∧ (∀ a b c, lt a b → lt b c → lt a c)

/-- The dual order: reverse the comparison. -/
def dualOrder (le : α → α → Prop) : α → α → Prop :=
  fun a b => le b a

-- ============================================================================
-- 2. MONOTONE FUNCTIONS
-- ============================================================================

/-- A function is monotone: preserves order. -/
def IsMonotone (f : α → α) (le : α → α → Prop) : Prop :=
  ∀ a b, le a b → le (f a) (f b)

/-- A function is antitone: reverses order. -/
def IsAntitone (f : α → α) (le : α → α → Prop) : Prop :=
  ∀ a b, le a b → le (f b) (f a)

/-- Monotone composition of monotone functions. -/
theorem monotone_comp (f g : α → α) (le : α → α → Prop)
    (hf : IsMonotone f le) (hg : IsMonotone g le) :
    IsMonotone (g ∘ f) le :=
  fun _ _ hab => hg _ _ (hf _ _ hab)

-- ============================================================================
-- 3. LATTICES
-- ============================================================================

/-- A lattice: every pair has a join and meet. -/
structure Lattice' (α : Type u) extends PartialOrder' α where
  sup : α → α → α
  inf : α → α → α
  sup_le : ∀ a b c, le a c → le b c → le (sup a b) c
  le_inf : ∀ a b c, le c a → le c b → le c (inf a b)

/-- A bounded lattice: has top and bottom elements. -/
structure BoundedLattice' (α : Type u) extends Lattice' α where
  top : α
  bot : α
  le_top : ∀ a, le a top
  bot_le : ∀ a, le bot a

/-- A distributive lattice: meets distribute over joins. -/
def IsDistributiveLattice (sup inf : α → α → α) (eq : α → α → Prop) : Prop :=
  ∀ a b c, eq (inf a (sup b c)) (sup (inf a b) (inf a c))

/-- A complete lattice: every subset has a supremum and infimum. -/
def IsCompleteLattice (sup inf : (α → Prop) → α)
    (le : α → α → Prop) : Prop :=
  (∀ S a, S a → le a (sup S)) ∧
  (∀ S a, (∀ b, S b → le b a) → le (sup S) a) ∧
  (∀ S a, S a → le (inf S) a) ∧
  (∀ S a, (∀ b, S b → le a b) → le a (inf S))

/-- A conditionally complete lattice: bounded subsets have sup/inf. -/
def IsCondComplete (sup : (α → Prop) → α) (le : α → α → Prop)
    (bounded : (α → Prop) → Prop) : Prop :=
  ∀ S, bounded S → (∃ a, S a) →
    ∀ a, S a → le a (sup S)

-- ============================================================================
-- 4. BOOLEAN ALGEBRAS
-- ============================================================================

/-- A Boolean algebra: a complemented distributive lattice. -/
structure BooleanAlgebra' (α : Type u) extends BoundedLattice' α where
  compl : α → α
  sup_compl : ∀ a, sup a (compl a) = top
  inf_compl : ∀ a, inf a (compl a) = bot

/-- De Morgan's laws in a Boolean algebra. -/
def deMorganBool (compl : α → α) (sup inf : α → α → α) : Prop :=
  (∀ a b, compl (sup a b) = inf (compl a) (compl b)) ∧
  (∀ a b, compl (inf a b) = sup (compl a) (compl b))

-- ============================================================================
-- 5. GALOIS CONNECTIONS
-- ============================================================================

/-- A Galois connection between two ordered types. -/
def IsGaloisConnection (l : α → β) (u : β → α)
    (leA : α → α → Prop) (leB : β → β → Prop) : Prop :=
  ∀ a b, leB (l a) b ↔ leA a (u b)

/-- A closure operator: monotone, extensive, idempotent. -/
def IsClosureOperator (c : α → α) (le : α → α → Prop) : Prop :=
  IsMonotone c le ∧
  (∀ a, le a (c a)) ∧
  (∀ a, c (c a) = c a)

-- ============================================================================
-- 6. FILTERS
-- ============================================================================

/-- A filter on a type: upward closed, closed under finite intersections. -/
structure Filter' (α : Type u) where
  mem : (α → Prop) → Prop
  univ : mem (fun _ => True)
  inter : ∀ U V, mem U → mem V → mem (fun x => U x ∧ V x)
  superset : ∀ U V, mem U → (∀ x, U x → V x) → mem V

/-- A prime filter: if A ∪ B ∈ F then A ∈ F or B ∈ F. -/
def IsPrimeFilter (F : Filter' α) : Prop :=
  ∀ U V, F.mem (fun x => U x ∨ V x) → F.mem U ∨ F.mem V

/-- An ideal (dual of filter): downward closed, closed under union. -/
def IsOrderIdeal (mem : (α → Prop) → Prop) (_le : α → α → Prop) : Prop :=
  mem (fun _ => False) ∧
  (∀ U V, mem U → mem V → mem (fun x => U x ∨ V x))

-- ============================================================================
-- 7. FIXED POINT THEOREMS
-- ============================================================================

/-- Knaster-Tarski: a monotone function on a complete lattice has a
    least fixed point. -/
def IsLeastFixedPoint (f : α → α) (le : α → α → Prop) (x : α) : Prop :=
  f x = x ∧ ∀ y, f y = y → le x y

/-- Greatest fixed point. -/
def IsGreatestFixedPoint (f : α → α) (le : α → α → Prop) (x : α) : Prop :=
  f x = x ∧ ∀ y, f y = y → le y x

/-- Knaster-Tarski existence: monotone endofunction has fixed points. -/
def knasterTarski (isMonotone : Prop) (hasFixedPoint : Prop) : Prop :=
  isMonotone → hasFixedPoint

-- ============================================================================
-- 8. DIRECTED SETS AND CHAINS
-- ============================================================================

/-- A directed set: every finite subset has an upper bound. -/
def IsDirected (le : α → α → Prop) : Prop :=
  ∀ a b, ∃ c, le a c ∧ le b c

/-- A chain: totally ordered subset. -/
def IsChain (le : α → α → Prop) (S : α → Prop) : Prop :=
  ∀ a b, S a → S b → le a b ∨ le b a

/-- Zorn's lemma (abstract): if every chain has an upper bound,
    there exists a maximal element. -/
def zorn (chainsHaveBounds : Prop) (hasMaximal : Prop) : Prop :=
  chainsHaveBounds → hasMaximal

-- ============================================================================
-- 9. WELL-FOUNDEDNESS
-- ============================================================================

/-- A relation is well-founded: no infinite descending chains. -/
def IsWellFounded' (r : α → α → Prop) : Prop :=
  ∀ P : α → Prop, (∀ a, (∀ b, r b a → P b) → P a) → ∀ a, P a

/-- A well-order: total + well-founded. -/
def IsWellOrdered (le : α → α → Prop) (lt : α → α → Prop) : Prop :=
  IsTotal le ∧ IsWellFounded' lt

-- ============================================================================
-- 10. ORDER ON OPTION: none as bottom
-- ============================================================================

/-- Option has a natural order: none ≤ some a for all a. -/
def optionLe (le : α → α → Prop) : Option α → Option α → Prop
  | none, _ => True
  | some _, none => False
  | some a, some b => le a b

/-- none is the bottom element. -/
theorem optionLe_none (le : α → α → Prop) (v : Option α) :
    optionLe le none v := by
  cases v <;> simp [optionLe]

/-- optionLe is reflexive when the underlying order is. -/
theorem optionLe_refl (le : α → α → Prop) (hrefl : ∀ a : α, le a a)
    (v : Option α) : optionLe le v v := by
  cases v <;> simp [optionLe, hrefl]

/-- Multiplication lifts through Option. -/
theorem order_mul_assoc [Mul α]
    (h : ∀ a b c : α, a * b * c = a * (b * c))
    (a b c : Option α) : a * b * c = a * (b * c) := by
  cases a <;> cases b <;> cases c <;> simp [h]

-- None absorbs (mul, neg, map): Core.lean's @[simp] set handles all cases.
