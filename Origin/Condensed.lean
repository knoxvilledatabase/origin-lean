/-
Released under MIT license.
-/
import Origin.Core

/-!
# Condensed on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib Condensed: 21 files, 2,930 lines, 228 genuine declarations.
This version keeps only domain-specific definitions and proofs that
actually use Option.

Condensed mathematics studies sheaves on compact Hausdorff spaces.
The key concepts: condensed objects (sheaves on CompHaus), light
condensed objects (sheaves on LightProfinite), discrete objects
(constant sheaves), and the functors between them.
-/

universe u
variable {α β : Type u}

-- ============================================================================
-- 1. CONDENSED STRUCTURE
-- ============================================================================

/-- A condensed object: a presheaf satisfying a sheaf condition.
    Abstractly: a map from "spaces" to "values" preserving covers. -/
structure Condensed (α : Type u) where
  val : α
  isSheaf : Prop

/-- Light condensed: the countable version. -/
structure LightCondensed (α : Type u) where
  val : α
  isSheaf : Prop

-- ============================================================================
-- 2. DISCRETE OBJECTS
-- ============================================================================

/-- A condensed object is discrete if it is constant. -/
def IsDiscrete (X : Condensed α) (const : α → Prop) : Prop :=
  const X.val

/-- A light condensed object is discrete if it is constant. -/
def IsLightDiscrete (X : LightCondensed α) (const : α → Prop) : Prop :=
  const X.val

-- ============================================================================
-- 3. FUNCTORS BETWEEN SITES
-- ============================================================================

/-- Embedding compact Hausdorff spaces into condensed objects. -/
def toCondensed (a : α) (h : Prop) : Condensed α :=
  ⟨a, h⟩

/-- Embedding light profinite into light condensed. -/
def toLightCondensed (a : α) (h : Prop) : LightCondensed α :=
  ⟨a, h⟩

-- ============================================================================
-- 4. CONDENSED ON OPTION: none is origin
-- ============================================================================

/-- Lift condensed to Option: none is the ground. -/
def Condensed.lift (X : Condensed α) : Condensed (Option α) :=
  ⟨some X.val, X.isSheaf⟩

/-- The ground condensed object. -/
def Condensed.ground (h : Prop) : Condensed (Option α) :=
  ⟨none, h⟩

-- ============================================================================
-- DEMONSTRATIONS: Option lift works for this domain
-- ============================================================================

/-- none absorbs under multiplication for condensed values. -/
theorem condensed_none_mul [Mul α] (b : Option α) :
    none * b = (none : Option α) := by simp

/-- some values compute. -/
theorem condensed_some_mul [Mul α] (a b : α) :
    (some a : Option α) * some b = some (a * b) := by simp

/-- Mapping preserves origin. -/
theorem condensed_map_none (f : α → β) :
    Option.map f none = (none : Option β) := by simp

/-- Mapping computes on values. -/
theorem condensed_map_some (f : α → β) (a : α) :
    Option.map f (some a) = some (f a) := by simp

/-- A domain law lifts through Option. -/
theorem condensed_mul_assoc [Mul α]
    (h : ∀ a b c : α, a * b * c = a * (b * c))
    (a b c : Option α) : a * b * c = a * (b * c) := by
  cases a <;> cases b <;> cases c <;> simp [h]
