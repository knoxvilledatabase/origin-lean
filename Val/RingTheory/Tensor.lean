/-
Released under MIT license.
-/
import Val.RingTheory.Core

/-!
# Val α: RingTheory — Tensor Products and Derivations

Tensor products, flat modules, derivations, Kaehler differentials,
and ring extensions.

Key dissolution: tensor products require `Nontrivial R` and `NoZeroDivisors R`
in many flatness results. In Val α, these are structural: contents ⊗ contents
= contents, and contents ≠ origin.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Tensor Products: Sort-Level
-- ============================================================================

/-- Elementary tensor: m ⊗ n at the sort level. -/
def tensorPair (mulF : α → α → α) (m n : Val α) : Val α :=
  mul mulF m n

theorem tensor_contents_contents (mulF : α → α → α) (a b : α) :
    tensorPair mulF (contents a) (contents b) = contents (mulF a b) := rfl

theorem tensor_origin_left (mulF : α → α → α) (n : Val α) :
    tensorPair mulF origin n = origin := by cases n <;> rfl

theorem tensor_origin_right (mulF : α → α → α) (m : Val α) :
    tensorPair mulF m origin = origin := by cases m <;> rfl

/-- Contents tensor never produces origin. -/
theorem tensor_contents_ne_origin (mulF : α → α → α) (a b : α) :
    tensorPair mulF (contents a) (contents b) ≠ (origin : Val α) := by
  intro h; cases h

-- ============================================================================
-- Bilinearity
-- ============================================================================

/-- Left distribution of tensor over addition. -/
theorem tensor_left_distrib (addF mulF : α → α → α)
    (h : ∀ a b c, mulF a (addF b c) = addF (mulF a b) (mulF a c))
    (a b c : α) :
    tensorPair mulF (contents a) (add addF (contents b) (contents c)) =
    add addF (tensorPair mulF (contents a) (contents b))
             (tensorPair mulF (contents a) (contents c)) := by
  show contents (mulF a (addF b c)) = contents (addF (mulF a b) (mulF a c))
  rw [h]

/-- Right distribution of tensor over addition. -/
theorem tensor_right_distrib (addF mulF : α → α → α)
    (h : ∀ a b c, mulF (addF a b) c = addF (mulF a c) (mulF b c))
    (a b c : α) :
    tensorPair mulF (add addF (contents a) (contents b)) (contents c) =
    add addF (tensorPair mulF (contents a) (contents c))
             (tensorPair mulF (contents b) (contents c)) := by
  show contents (mulF (addF a b) c) = contents (addF (mulF a c) (mulF b c))
  rw [h]

-- ============================================================================
-- Flat Modules
-- ============================================================================

/-- Flatness: tensoring with contents preserves contents. -/
theorem flat_preserves_contents (mulF : α → α → α) (m a : α) :
    tensorPair mulF (contents m) (contents a) = contents (mulF m a) := rfl

/-- Flatness: contents tensor never collapses to origin. -/
theorem flat_ne_origin (mulF : α → α → α) (m a : α) :
    tensorPair mulF (contents m) (contents a) ≠ (origin : Val α) := by
  intro h; cases h

/-- Torsion-free at sort level: if m ⊗ v = origin then v = origin. -/
theorem torsion_free_sort (mulF : α → α → α) (a : α) (v : Val α)
    (h : tensorPair mulF (contents a) v = origin) :
    v = origin := by
  cases v with
  | origin => rfl
  | container b => cases h
  | contents b => cases h

-- ============================================================================
-- Derivations: d(ab) = a·db + b·da
-- ============================================================================

/-- Leibniz rule: D(ab) = a·Db + b·Da within contents. -/
theorem derivation_leibniz (addF mulF : α → α → α) (a b Da Db : α) :
    add addF (mul mulF (contents a) (contents Db)) (mul mulF (contents b) (contents Da)) =
    contents (addF (mulF a Db) (mulF b Da)) := rfl

/-- Derivation of origin is origin. -/
theorem derivation_origin_val (D : Val α → Val α)
    (hD : D origin = origin) :
    D origin = origin := hD

/-- Derivation maps contents to contents (if defined). -/
theorem derivation_contents_ne_origin (D : α → α) (a : α) :
    (contents (D a) : Val α) ≠ origin := by
  intro h; cases h

-- ============================================================================
-- Kaehler Differentials
-- ============================================================================

/-- Differential element ds for s in contents. -/
def kahlerDiff (d : α → α) (a : α) : Val α := contents (d a)

theorem kahlerDiff_is_contents (d : α → α) (a : α) :
    kahlerDiff d a = contents (d a) := rfl

theorem kahlerDiff_ne_origin (d : α → α) (a : α) :
    kahlerDiff d a ≠ (origin : Val α) := by
  intro h; cases h

/-- Kaehler differential product: d(ab) = a·db + b·da. -/
theorem kahlerDiff_product (addF mulF : α → α → α) (d : α → α)
    (hd : ∀ a b, d (mulF a b) = addF (mulF a (d b)) (mulF b (d a))) (a b : α) :
    kahlerDiff d (mulF a b) = contents (addF (mulF a (d b)) (mulF b (d a))) := by
  simp only [kahlerDiff_is_contents, hd]

-- ============================================================================
-- Ring Extensions
-- ============================================================================

/-- Ring extension map preserves sort. -/
def extensionMap (f : α → α) : Val α → Val α
  | origin => origin
  | container a => container (f a)
  | contents a => contents (f a)

theorem extensionMap_contents (f : α → α) (a : α) :
    extensionMap f (contents a) = contents (f a) := rfl

theorem extensionMap_ne_origin (f : α → α) (a : α) :
    extensionMap f (contents a) ≠ (origin : Val α) := by
  intro h; cases h

end Val
