/-
Released under MIT license.
-/
import Val.Topology.Connected
import Val.Topology.Continuous

/-!
# Val α: Homotopy Theory

Homotopy, fundamental group, covering spaces (sort-level).
The key: homotopies between contents-valued maps stay in contents.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Homotopy Between Maps
-- ============================================================================

/-- A homotopy between two maps f, g : α → α.
    H(0, x) = f(x), H(1, x) = g(x). Parametrized by a "time" index (Nat). -/
def isHomotopy (H : Nat → α → α) (f g : α → α) : Prop :=
  (∀ x, H 0 x = f x) ∧ (∀ x, H 1 x = g x)

/-- A homotopy between contents-valued maps stays in contents. -/
theorem homotopy_contents (H : Nat → α → α) (f g : α → α)
    (hH : isHomotopy H f g) (t : Nat) (x : α) :
    ∃ r, (contents (H t x) : Val α) = contents r := ⟨H t x, rfl⟩

/-- Homotopy never touches origin. -/
theorem homotopy_ne_origin (H : Nat → α → α) (t : Nat) (x : α) :
    (contents (H t x) : Val α) ≠ origin := by simp

/-- Homotopy at t=0 gives f, at t=1 gives g. Lifted to Val. -/
theorem homotopy_endpoints (H : Nat → α → α) (f g : α → α)
    (hH : isHomotopy H f g) (x : α) :
    (contents (H 0 x) : Val α) = contents (f x) ∧
    (contents (H 1 x) : Val α) = contents (g x) := by
  constructor
  · show contents (H 0 x) = contents (f x); rw [hH.1]
  · show contents (H 1 x) = contents (g x); rw [hH.2]

-- ============================================================================
-- Homotopy Equivalence
-- ============================================================================

/-- Two types are homotopy equivalent via maps f, g with homotopies. -/
def homotopyEquiv (f : α → α) (g : α → α)
    (H₁ : Nat → α → α) (H₂ : Nat → α → α) : Prop :=
  isHomotopy H₁ (g ∘ f) id ∧ isHomotopy H₂ (f ∘ g) id

/-- Homotopy equivalence lifts to Val α within contents. -/
theorem homotopy_equiv_contents (f g : α → α)
    (H₁ H₂ : Nat → α → α)
    (h : homotopyEquiv f g H₁ H₂) (a : α) :
    (∃ r, valMap (g ∘ f) (contents a) = contents r) ∧
    (∃ r, valMap (f ∘ g) (contents a) = contents r) :=
  ⟨⟨g (f a), rfl⟩, ⟨f (g a), rfl⟩⟩

-- ============================================================================
-- Fundamental Group (Sort-Level)
-- ============================================================================

/-- A loop based at a point: path(0) = path(end) = basepoint. -/
def isLoop (path : Nat → α) (base : α) (endpoint : Nat) : Prop :=
  path 0 = base ∧ path endpoint = base

/-- Loops in contents stay in contents. -/
theorem loop_contents (path : Nat → α) (base : α) (endpoint : Nat)
    (h : isLoop path base endpoint) (n : Nat) :
    ∃ r, (contents (path n) : Val α) = contents r := ⟨path n, rfl⟩

/-- Loop composition: concatenate two loops. -/
def loopConcat (p q : Nat → α) (mid : Nat) : Nat → α :=
  fun n => if n ≤ mid then p n else q (n - mid)

/-- Loop composition stays in contents. -/
theorem loopConcat_contents (p q : Nat → α) (mid : Nat) (n : Nat) :
    ∃ r, (contents (loopConcat p q mid n) : Val α) = contents r :=
  ⟨loopConcat p q mid n, rfl⟩

-- ============================================================================
-- Contractibility
-- ============================================================================

/-- A space is contractible if the identity is homotopic to a constant map. -/
def isContractible (pt : α) (H : Nat → α → α) : Prop :=
  isHomotopy H id (fun _ => pt)

/-- Contractibility lifts: the contraction stays in contents. -/
theorem contractible_contents (pt : α) (H : Nat → α → α)
    (h : isContractible pt H) (t : Nat) (x : α) :
    ∃ r, (contents (H t x) : Val α) = contents r := ⟨H t x, rfl⟩

/-- The contraction point is contents. -/
theorem contraction_point_contents (pt : α) :
    (contents pt : Val α) ≠ origin := by simp

-- ============================================================================
-- Covering Spaces (Sort-Level)
-- ============================================================================

/-- A covering map: a sort-preserving surjection. Lifts through valMap. -/
theorem covering_preserves_contents (p : α → α) (a : α) :
    valMap p (contents a) = contents (p a) := rfl

/-- Covering maps send origin to origin. -/
theorem covering_preserves_origin (p : α → α) :
    valMap p (origin : Val α) = (origin : Val α) := rfl

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Homotopy theory over Val α:
--   ✓ Homotopies between contents maps stay in contents
--   ✓ Homotopy endpoints lift correctly
--   ✓ Homotopy equivalence lifts to Val α
--   ✓ Fundamental group: loops in contents stay in contents
--   ✓ Loop composition preserves contents
--   ✓ Contractibility lifts to Val α
--   ✓ Covering spaces: sort-preserving
--
-- Zero sorries. Zero typeclasses. Zero Mathlib.

end Val
