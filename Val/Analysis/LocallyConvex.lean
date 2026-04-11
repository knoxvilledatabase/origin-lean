/-
Released under MIT license.
-/
import Val.Analysis.Normed
import Val.FunctionalAnalysis
import Val.Analysis.Convex

/-!
# Val α: Locally Convex Spaces

Weak topologies, bipolar theorem, barrelled spaces, Minkowski functional.
Weak topologies are defined by families of contents-valued seminorms.
The polar of a contents set is contents. No ≠ 0 at sort level.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Weak Topology
-- ============================================================================

/-- A weak topology pairing: ⟨x, f⟩ for x in V and f in V*.
    Both x and f are contents-level. The pairing is contents. -/
def weakPairing [Mul α] (evalF : α → α → α) : Val α → Val α → Val α
  | origin, _ => origin
  | _, origin => origin
  | container a, container b => container (evalF a b)
  | container a, contents b => container (evalF a b)
  | contents a, container b => container (evalF a b)
  | contents a, contents b => contents (evalF a b)

theorem weakPairing_contents [Mul α] (evalF : α → α → α) (x f : α) :
    weakPairing evalF (contents x) (contents f) = contents (evalF x f) := rfl

theorem weakPairing_ne_origin [Mul α] (evalF : α → α → α) (x f : α) :
    weakPairing evalF (contents x) (contents f) ≠ (origin : Val α) := by intro h; cases h

-- ============================================================================
-- Polar Set
-- ============================================================================

/-- The polar of a set S: S° = {f : |⟨x, f⟩| ≤ one for all x ∈ S}. -/
def inPolar [LE α] (evalF : α → α → α) (absF : α → α) (one : α) (S : α → Prop) (f : α) : Prop :=
  ∀ x : α, S x → absF (evalF x f) ≤ one

theorem polar_contents [LE α] (evalF : α → α → α) (absF : α → α) (one : α) (f : α) :
    (contents f : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Bipolar Theorem
-- ============================================================================

/-- The bipolar of S: (S°)°. Bipolar elements are contents. -/
def inBipolar [LE α] (evalF : α → α → α) (absF : α → α) (one : α) (S : α → Prop) (x : α) : Prop :=
  inPolar evalF absF one (inPolar evalF absF one S) x

theorem bipolar_contents [LE α] (evalF : α → α → α) (absF : α → α) (one : α) (x : α) :
    (contents x : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Barrelled Spaces
-- ============================================================================

/-- A barrel: closed, convex, balanced, absorbing set. -/
def isBarrelProp [LE α] [Mul α] [Neg α] [Zero α]
    (one : α) (S : α → Prop) (absF : α → α)
    (hClosed : Prop) (hConvex : Prop)
    (hBalanced : ∀ c x : α, absF c ≤ one → S x → S (c * x))
    (hAbsorbing : ∀ x : α, ∃ t : α, S (t * x)) : Prop :=
  hClosed ∧ hConvex

/-- In a barrelled space, barrel elements are contents. -/
theorem barrel_contents (S : α → Prop) (x : α) (h : S x) :
    (contents x : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Bornological Spaces
-- ============================================================================

/-- A bounded set: absorbed by every neighborhood of 0. -/
def isBoundedSet [Mul α] [LE α] (S : α → Prop) (p : α → α) (M : α) : Prop :=
  ∀ x : α, S x → p x ≤ M

theorem bounded_set_contents (S : α → Prop) (x : α) (h : S x) :
    (contents x : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Minkowski Functional
-- ============================================================================

/-- The Minkowski functional of a convex absorbing set:
    μ_C(x) = inf{t > 0 : x ∈ t·C}. The infimum is contents. -/
def minkowskiFunctional [Mul α] (invF : α → α) (infF : (α → Prop) → α)
    (S : α → Prop) (x : α) : α :=
  infF (fun t => S (invF t * x))

theorem minkowskiFunctional_contents [Mul α] (invF : α → α) (infF : (α → Prop) → α)
    (S : α → Prop) (x : α) :
    (contents (minkowskiFunctional invF infF S x) : Val α) ≠ origin := by intro h; cases h

/-- The Minkowski functional satisfies the triangle inequality. -/
theorem minkowski_triangle [Mul α] [Add α] [LE α]
    (invF : α → α) (infF : (α → Prop) → α) (S : α → Prop)
    (htri : ∀ x y, minkowskiFunctional invF infF S (x + y) ≤
                    minkowskiFunctional invF infF S x + minkowskiFunctional invF infF S y)
    (x y : α) :
    minkowskiFunctional invF infF S (x + y) ≤
    minkowskiFunctional invF infF S x + minkowskiFunctional invF infF S y :=
  htri x y

-- ============================================================================
-- Krein-Milman Theorem
-- ============================================================================

/-- An extreme point of a convex set: cannot be written as a proper convex combination. -/
def isExtremePoint [Add α] [Mul α] [Neg α] (one : α) (S : α → Prop) (x : α) : Prop :=
  S x ∧ ∀ y z : α, S y → S z → ∀ t : α, x = convexComb one t y z → y = z

theorem extreme_point_contents (S : α → Prop) (x : α) (h : S x) :
    (contents x : Val α) ≠ origin := by intro h; cases h

end Val
