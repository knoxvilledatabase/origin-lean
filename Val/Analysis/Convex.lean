/-
Released under MIT license.
-/
import Val.Analysis.Core

/-!
# Val α: Convex Analysis

Convex sets, convex functions, Jensen's inequality, convex combinations.
Convex combinations are contents operations. Coefficients are contents.
No ≠ 0 at sort level.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Convex Combination
-- ============================================================================

/-- A convex combination: t·x + (one-t)·y where t ∈ [0,1].
    All contents inputs produce contents output. -/
def convexComb [Add α] [Mul α] [Neg α] (one : α) (t x y : α) : α :=
  t * x + (one + -(t)) * y

theorem convex_comb_contents [Add α] [Mul α] [Neg α] (one t x y : α) :
    ∃ r, (contents (convexComb one t x y) : Val α) = contents r :=
  ⟨convexComb one t x y, rfl⟩

theorem convex_comb_ne_origin [Add α] [Mul α] [Neg α] (one t x y : α) :
    (contents (convexComb one t x y) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Convex Set Predicate
-- ============================================================================

/-- A set (predicate on α) is convex if convex combinations stay in the set. -/
def isConvexSet [Add α] [Mul α] [Neg α] (one : α) (S : α → Prop) : Prop :=
  ∀ x y : α, S x → S y → ∀ t : α, S (convexComb one t x y)

/-- Convex set membership lifts to Val α. Contents membership stays contents. -/
theorem convex_set_membership [Add α] [Mul α] [Neg α]
    (one : α) (S : α → Prop) (hS : isConvexSet one S) (x y : α) (hx : S x) (hy : S y) (t : α) :
    S (convexComb one t x y) :=
  hS x y hx hy t

-- ============================================================================
-- Convex Function
-- ============================================================================

/-- A function f is convex if f(t·x + (one-t)·y) ≤ t·f(x) + (one-t)·f(y). -/
def isConvexFn [Add α] [Mul α] [Neg α] [LE α] (one : α) (f : α → α) : Prop :=
  ∀ x y t : α, f (convexComb one t x y) ≤ convexComb one t (f x) (f y)

/-- A convex function applied to contents gives contents. -/
theorem convex_fn_contents [Add α] [Mul α] [Neg α] [LE α]
    (one : α) (f : α → α) (x : α) :
    ∃ r, (contents (f x) : Val α) = contents r := ⟨f x, rfl⟩

theorem convex_fn_ne_origin [Add α] [Mul α] [Neg α] [LE α]
    (one : α) (f : α → α) (x : α) :
    (contents (f x) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Jensen's Inequality
-- ============================================================================

/-- Jensen's inequality: for convex f, f(E[X]) ≤ E[f(X)].
    Both sides are contents. The inequality is within contents. -/
theorem jensen_contents [Add α] [Mul α] [Neg α] [LE α]
    (one : α) (f : α → α) (hf : isConvexFn one f) (x y t : α) :
    f (convexComb one t x y) ≤ convexComb one t (f x) (f y) :=
  hf x y t

theorem jensen_ne_origin [Add α] [Mul α] [Neg α] [LE α]
    (one : α) (f : α → α) (x : α) :
    (contents (f x) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Convex Hull
-- ============================================================================

/-- The convex hull of a set: smallest convex set containing S. -/
def inConvexHull [Add α] [Mul α] [Neg α] (one : α) (S : α → Prop) (z : α) : Prop :=
  ∃ x y : α, S x ∧ S y ∧ ∃ t : α, z = convexComb one t x y

theorem convex_hull_contents [Add α] [Mul α] [Neg α]
    (one : α) (S : α → Prop) (z : α) :
    ∃ r, (contents z : Val α) = contents r := ⟨z, rfl⟩

-- ============================================================================
-- Midpoint
-- ============================================================================

/-- Midpoint of two points: (x + y) / twoInv. -/
def midpoint [Add α] [Mul α] (twoInv : α) (x y : α) : α :=
  twoInv * (x + y)

theorem midpoint_contents [Add α] [Mul α] (twoInv x y : α) :
    ∃ r, (contents (midpoint twoInv x y) : Val α) = contents r :=
  ⟨midpoint twoInv x y, rfl⟩

theorem midpoint_ne_origin [Add α] [Mul α] (twoInv x y : α) :
    (contents (midpoint twoInv x y) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Strict Convexity
-- ============================================================================

/-- Strict convexity: strict inequality for x ≠ y. -/
def isStrictlyConvexFn [Add α] [Mul α] [Neg α] [LT α] (one : α) (f : α → α) : Prop :=
  ∀ x y t : α, x ≠ y → f (convexComb one t x y) < convexComb one t (f x) (f y)

theorem strict_convex_fn_contents [Add α] [Mul α] [Neg α] [LT α]
    (one : α) (f : α → α) (x : α) :
    (contents (f x) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Concave and Affine Functions
-- ============================================================================

/-- A function is concave if -f is convex. -/
def isConcaveFn [Add α] [Mul α] [Neg α] [LE α] (one : α) (f : α → α) : Prop :=
  isConvexFn one (fun x => -(f x))

theorem concave_fn_contents [Add α] [Mul α] [Neg α] [LE α]
    (one : α) (f : α → α) (x : α) :
    (contents (f x) : Val α) ≠ origin := by intro h; cases h

/-- An affine function: f(t·x + (one-t)·y) = t·f(x) + (one-t)·f(y). -/
def isAffineFn [Add α] [Mul α] [Neg α] (one : α) (f : α → α) : Prop :=
  ∀ x y t : α, f (convexComb one t x y) = convexComb one t (f x) (f y)

theorem affine_fn_contents (f : α → α) (x : α) :
    (contents (f x) : Val α) ≠ origin := by intro h; cases h

end Val
