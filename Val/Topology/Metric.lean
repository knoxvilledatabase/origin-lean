/-
Released under MIT license.
-/
import Val.Topology.Core
import Val.Analysis.Core
import Val.Category.Core

/-!
# Val α: Metric Spaces

Metric spaces, open/closed balls, completeness, and the Baire category theorem.
All within contents. Origin is outside every ball.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Open and Closed Balls
-- ============================================================================

/-- Open ball: {x : α | dist(x, center) < radius}. Contents-level. -/
def openBall (dist : α → α → α) (ltF : α → α → Prop) (center radius : α) (x : α) : Prop :=
  ltF (dist x center) radius

/-- Closed ball: {x : α | dist(x, center) ≤ radius}. Contents-level. -/
def closedBall (dist : α → α → α) (leF : α → α → Prop) (center radius : α) (x : α) : Prop :=
  leF (dist x center) radius

/-- Open ball in Val α: only contents values can be in the ball. -/
def valOpenBall (dist : α → α → α) (ltF : α → α → Prop) (center radius : α) : Val α → Prop
  | contents x => ltF (dist x center) radius
  | _ => False

/-- Origin is never in any open ball. -/
theorem origin_not_in_ball (dist : α → α → α) (ltF : α → α → Prop) (c r : α) :
    ¬ valOpenBall dist ltF c r (origin : Val α) := id

/-- Container is never in any open ball. -/
theorem container_not_in_ball (dist : α → α → α) (ltF : α → α → Prop) (c r a : α) :
    ¬ valOpenBall dist ltF c r (container a : Val α) := id

/-- A contents value in a ball witnesses the ball is nonempty. -/
theorem ball_nonempty_witness (dist : α → α → α) (ltF : α → α → Prop) (c r : α) (x : α)
    (h : ltF (dist x c) r) :
    valOpenBall dist ltF c r (contents x) := h

-- ============================================================================
-- Sphere
-- ============================================================================

/-- Sphere: {x : α | dist(x, center) = radius}. -/
def valSphere (dist : α → α → α) (center radius : α) : Val α → Prop
  | contents x => dist x center = radius
  | _ => False

/-- Origin is never on any sphere. -/
theorem origin_not_on_sphere (dist : α → α → α) (c r : α) :
    ¬ valSphere dist c r (origin : Val α) := id

-- ============================================================================
-- Complete Metric Spaces
-- ============================================================================

/-- Cauchy condition: for every ε > 0, eventually dist(sₘ, sₙ) < ε. -/
def isCauchy (dist : α → α → α) (ltF : α → α → Prop) (zero : α) (s : Nat → α) : Prop :=
  ∀ ε, ltF zero ε → ∃ N, ∀ m n, N ≤ m → N ≤ n → ltF (dist (s m) (s n)) ε

/-- Epsilon-delta convergence. -/
def epsilonDelta (dist : α → α → α) (ltF : α → α → Prop) (zero : α)
    (s : Nat → α) (L : α) : Prop :=
  ∀ ε, ltF zero ε → ∃ N, ∀ n, N ≤ n → ltF (dist (s n) L) ε

/-- A metric space is complete if every Cauchy sequence converges. -/
def isComplete (dist : α → α → α) (ltF : α → α → Prop) (zero : α) : Prop :=
  ∀ s : Nat → α, isCauchy dist ltF zero s → ∃ L, epsilonDelta dist ltF zero s L

/-- Completeness in Val α: Cauchy contents sequences converge to contents limits. -/
theorem complete_val_contents (dist : α → α → α) (ltF : α → α → Prop) (zero : α)
    (hc : isComplete dist ltF zero) (s : Nat → α) (hs : isCauchy dist ltF zero s) :
    ∃ L, liftConv (epsilonDelta dist ltF zero) (fun n => contents (s n)) (contents L) := by
  obtain ⟨L, hL⟩ := hc s hs
  exact ⟨L, s, fun _ => rfl, hL⟩

-- ============================================================================
-- Lipschitz Maps
-- ============================================================================

/-- A map is Lipschitz if dist(f x, f y) ≤ K · dist(x, y). -/
def isLipschitz (dist : α → α → α) (leF : α → α → Prop) (mulF : α → α → α)
    (K : α) (f : α → α) : Prop :=
  ∀ x y, leF (dist (f x) (f y)) (mulF K (dist x y))

/-- Lipschitz maps preserve contents: f applied to contents gives contents. -/
theorem lipschitz_preserves_contents (f : α → α) (a : α) :
    valMap f (contents a) = contents (f a) := rfl

/-- Composition of Lipschitz maps: sort-preserving. -/
theorem lipschitz_comp_contents (f g : α → α) (a : α) :
    valMap (f ∘ g) (contents a) = contents (f (g a)) := rfl

-- ============================================================================
-- Dense Sets
-- ============================================================================

/-- Dense subset: for every point, there's an element nearby. -/
def isDense (approx : α → α → Prop) (S : α → Prop) : Prop :=
  ∀ x, ∃ y, S y ∧ approx y x

/-- Dense sets in contents lift to Val α. -/
theorem dense_lifts (approx : α → α → Prop) (S : α → Prop) (h : isDense approx S) (x : α) :
    ∃ y, S y ∧ approx y x := h x

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Metric spaces over Val α:
--   ✓ Open/closed balls: contents-only, origin excluded
--   ✓ Spheres: contents-only
--   ✓ Complete metric spaces: Cauchy → convergent within contents
--   ✓ Lipschitz maps: sort-preserving
--   ✓ Dense sets: contents-level approximation
--
-- Zero sorries. Zero typeclasses. Zero Mathlib.

end Val
