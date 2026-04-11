/-
Released under MIT license.
-/
import Val.RingTheory.Core

/-!
# Val α: RingTheory — Graded and Filtered Structures

Graded algebras, filtrations, divided powers, and Witt vectors.

Graded algebra: R = ⊕ Rₙ with RₘRₙ ⊆ Rₘ₊ₙ. Filtered algebra: increasing
sequence of subsets. Witt vectors: arithmetic on infinite sequences.

Key dissolution: each graded component requires `Nontrivial` conditions in
Mathlib. In Val α, each component lives in contents. Structural.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Graded Algebra: R = ⊕ Rₙ
-- ============================================================================

/-- Graded component: elements of degree n. -/
def gradedComponent (grade : α → Nat) (n : Nat) : α → Prop :=
  fun a => grade a = n

/-- Elements in a graded component are in contents. -/
theorem graded_ne_origin (grade : α → Nat) (n : Nat) (a : α)
    (ha : gradedComponent grade n a) :
    (contents a : Val α) ≠ origin := by
  intro h; cases h

/-- Origin is outside every graded component. -/
theorem origin_not_graded (grade : α → Nat) (n : Nat) :
    ¬ inIdeal (gradedComponent grade n) (origin : Val α) := id

/-- Product of graded elements: degrees add. -/
theorem graded_mul (mulF : α → α → α) (grade : α → Nat) (m n : Nat)
    (hGrade : ∀ a b, grade (mulF a b) = grade a + grade b)
    (a b : α) (ha : gradedComponent grade m a) (hb : gradedComponent grade n b) :
    gradedComponent grade (m + n) (mulF a b) := by
  show grade (mulF a b) = m + n
  rw [hGrade, ha, hb]

-- ============================================================================
-- Filtered Algebra
-- ============================================================================

/-- Filtration: increasing sequence of subsets. -/
def filtration (F : Nat → α → Prop) : Prop :=
  ∀ n a, F n a → F (n + 1) a

/-- Filtered elements are in contents. -/
theorem filtered_ne_origin (F : Nat → α → Prop) (n : Nat) (a : α)
    (ha : F n a) :
    (contents a : Val α) ≠ origin := by
  intro h; cases h

/-- Filtration compatible with products. -/
theorem filtered_mul (mulF : α → α → α) (F : Nat → α → Prop)
    (hF : ∀ m n a b, F m a → F n b → F (m + n) (mulF a b))
    (m n : Nat) (a b : α) (ha : F m a) (hb : F n b) :
    inIdeal (F (m + n)) (mul mulF (contents a) (contents b)) := by
  show F (m + n) (mulF a b)
  exact hF m n a b ha hb

-- ============================================================================
-- Divided Powers
-- ============================================================================

/-- Divided power operation γₙ(a) = aⁿ/n! (formal). -/
def dividedPower (gamma : Nat → α → α) : Nat → Val α → Val α
  | _, origin => origin
  | n, container a => container (gamma n a)
  | n, contents a => contents (gamma n a)

theorem dividedPower_contents (gamma : Nat → α → α) (n : Nat) (a : α) :
    dividedPower gamma n (contents a) = contents (gamma n a) := rfl

theorem dividedPower_origin (gamma : Nat → α → α) (n : Nat) :
    dividedPower gamma n (origin : Val α) = origin := rfl

theorem dividedPower_ne_origin (gamma : Nat → α → α) (n : Nat) (a : α) :
    dividedPower gamma n (contents a) ≠ (origin : Val α) := by
  intro h; cases h

/-- Divided power product rule: γₘ · γₙ = C(m+n,m) · γₘ₊ₙ within contents. -/
theorem dividedPower_mul (mulF : α → α → α) (gamma : Nat → α → α)
    (binom : Nat → Nat → α)
    (hDP : ∀ m n a, mulF (gamma m a) (gamma n a) = mulF (binom (m + n) m) (gamma (m + n) a))
    (m n : Nat) (a : α) :
    mul mulF (contents (gamma m a)) (contents (gamma n a)) =
    contents (mulF (binom (m + n) m) (gamma (m + n) a)) := by
  show contents (mulF (gamma m a) (gamma n a)) = contents (mulF (binom (m + n) m) (gamma (m + n) a))
  rw [hDP]

-- ============================================================================
-- Witt Vectors
-- ============================================================================

/-- Witt vector component access. -/
def wittComponent (n : Nat) (components : Nat → Val α) : Val α :=
  components n

theorem witt_contents_component (f : Nat → α) (n : Nat) :
    wittComponent n (fun i => contents (f i)) = contents (f n) := rfl

theorem witt_origin_component (n : Nat) :
    wittComponent n (fun _ => (origin : Val α)) = origin := rfl

/-- Witt vector component is never origin if all components are contents. -/
theorem witt_ne_origin (f : Nat → α) (n : Nat) :
    wittComponent n (fun i => contents (f i)) ≠ (origin : Val α) := by
  intro h; cases h

/-- Witt addition: componentwise (simplified). -/
theorem witt_add (addF : α → α → α) (f g : Nat → α) (n : Nat) :
    add addF (contents (f n)) (contents (g n)) = contents (addF (f n) (g n)) := rfl

/-- Ghost map component: always contents. -/
theorem ghost_map_ne_origin (ghost : (Nat → α) → Nat → α) (f : Nat → α) (n : Nat) :
    (contents (ghost f n) : Val α) ≠ origin := by
  intro h; cases h

end Val
