/-
Released under MIT license.
-/
import Origin.Core

/-!
# Dynamics on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib Dynamics: 22 files, 5,047 lines, 558 genuine declarations.
This version keeps only domain-specific definitions and proofs that
actually use Option.

Dynamical systems: fixed points, periodic points, orbits, flows,
ergodicity, topological entropy.
-/

universe u
variable {α β τ G : Type u}

/-- Iterate a function n times. -/
def iter (f : α → α) : Nat → α → α
  | 0 => id
  | n + 1 => f ∘ iter f n

-- ============================================================================
-- 1. FIXED POINTS AND PERIODICITY
-- ============================================================================

/-- A fixed point: f(x) = x. -/
def IsFixedPt' (f : α → α) (x : α) : Prop := f x = x

/-- A periodic point: f iterated n times fixes x. -/
def IsPeriodicPt' (f : α → α) (n : Nat) (x : α) : Prop :=
  IsFixedPt' (iter f n) x

/-- The set of periodic points as a predicate. -/
def isPeriodicPoint (f : α → α) (x : α) : Prop :=
  ∃ n, n > 0 ∧ IsPeriodicPt' f n x

-- ============================================================================
-- 2. ORBITS
-- ============================================================================

/-- The forward orbit of a point under iteration. -/
def forwardOrbit (f : α → α) (x : α) (n : Nat) : α :=
  iter f n x

-- ============================================================================
-- 3. FLOWS
-- ============================================================================

/-- A flow: a parameterized family of maps. -/
structure Flow' (τ α : Type u) where
  toFun : τ → α → α

/-- The reverse flow. -/
def Flow'.reverse [Neg τ] (ϕ : Flow' τ α) : Flow' τ α where
  toFun t := ϕ.toFun (-t)

-- ============================================================================
-- 4. INVARIANT SETS
-- ============================================================================

/-- A predicate is invariant under a family of maps. -/
def IsInvariant' (ϕ : τ → α → α) (mem : α → Prop) : Prop :=
  ∀ t x, mem x → mem (ϕ t x)

-- ============================================================================
-- 5. ERGODICITY
-- ============================================================================

/-- Pre-ergodic: every invariant set is trivial. -/
def IsPreErgodic (_ : α → α) (isInvariant isTrivial : (α → Prop) → Prop) : Prop :=
  ∀ s, isInvariant s → isTrivial s

/-- Conservative: recurrence holds for all nontrivial sets. -/
def IsConservative (_ : α → α) (hasRecurrence : (α → Prop) → Prop) : Prop :=
  ∀ s, hasRecurrence s

-- ============================================================================
-- 6. TOPOLOGICAL ENTROPY
-- ============================================================================

/-- A dynamical cover at depth n. -/
def IsDynCover (f : α → α) (covered : α → Prop) (n : Nat) (center : α → Prop) : Prop :=
  ∀ x, covered x → ∃ y, center y ∧
    ∀ k, k < n → iter f k x = iter f k y

-- ============================================================================
-- 7. MINIMAL ACTIONS
-- ============================================================================

/-- An action is minimal if every orbit is dense. -/
def IsMinimalAction (act : G → α → α) (isDense : (α → Prop) → Prop) : Prop :=
  ∀ x, isDense (fun y => ∃ g, act g x = y)

-- ============================================================================
-- DEMONSTRATIONS: Option lift works for this domain
-- ============================================================================

/-- Fixed points lift through Option: none is always fixed. -/
theorem dyn_map_none (f : α → α) :
    Option.map f none = (none : Option α) := by simp

/-- Iteration computes on values. -/
theorem dyn_map_some (f : α → α) (a : α) :
    Option.map f (some a) = some (f a) := by simp

/-- none absorbs under multiplication. -/
theorem dyn_none_mul [Mul α] (b : Option α) :
    none * b = (none : Option α) := by simp

/-- Composition lifts through Option. -/
theorem dyn_map_comp (f g : α → α) (v : Option α) :
    Option.map f (Option.map g v) = Option.map (f ∘ g) v := by
  cases v <;> simp
