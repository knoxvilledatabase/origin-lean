/-
Released under MIT license.
-/
import Origin.Core

/-!
# Topology on Option α (Core-based)

Val/Topology.lean: 525 lines. Open sets, continuity, compactness,
connectedness, metric spaces, filters, order theory, homotopy, sheaves.

This version keeps only domain-specific definitions and proofs that
actually use Option.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. OPEN SETS (Alexandroff compactification)
-- ============================================================================

def IsOpenC (openα : (α → Prop) → Prop) (compactα : (α → Prop) → Prop)
    (U : Option α → Prop) : Prop :=
  openα (fun a => U (some a)) ∧
  (U none → compactα (fun a => ¬ U (some a)))

-- continuous_comp, continuous_id: composition/identity patterns, derivable from Core.

-- ============================================================================
-- 2. METRIC SPACES
-- ============================================================================

def IsLipschitz (f : α → α) (K : α) (distF : α → α → α) (leF : α → α → Prop)
    (mulF : α → α → α) : Prop :=
  ∀ a b, leF (distF (f a) (f b)) (mulF K (distF a b))

def IsIsometry (f : α → α) (distF : α → α → α) : Prop :=
  ∀ a b, distF (f a) (f b) = distF a b

-- ============================================================================
-- 4. FILTERS AND CONVERGENCE
-- ============================================================================

structure OptFilter (α : Type u) where
  sets : (Option α → Prop) → Prop
  univ_mem : sets (fun _ => True)
  superset : ∀ U V, sets U → (∀ x, U x → V x) → sets V
  inter_mem : ∀ U V, sets U → sets V → sets (fun x => U x ∧ V x)

def IsUltrafilter (F : OptFilter α) : Prop :=
  (¬ F.sets (fun _ => False)) ∧
  ∀ U : Option α → Prop, F.sets U ∨ F.sets (fun x => ¬ U x)

-- ============================================================================
-- 5. ORDER THEORY
-- ============================================================================

def IsGaloisConnection (l u : α → α) (leF : α → α → Prop) : Prop :=
  ∀ a b, leF (l a) b ↔ leF a (u b)

def IsWellOrder (leF : α → α → Prop) : Prop :=
  ∀ S : α → Prop, (∃ a, S a) → ∃ m, S m ∧ ∀ a, S a → leF m a

-- ============================================================================
-- 6. HOMOTOPY
-- ============================================================================

def FundGroupElem (basepoint : α) (loop : α → α) : Prop :=
  loop basepoint = basepoint

theorem fund_group_comp (bp : α) (l₁ l₂ : α → α)
    (h₁ : FundGroupElem bp l₁) (h₂ : FundGroupElem bp l₂) :
    FundGroupElem bp (l₁ ∘ l₂) := by
  simp [FundGroupElem, Function.comp] at *; rw [h₂, h₁]

def IsCoveringMap (p : α → α) (local_inv : α → α) : Prop :=
  ∀ a, p (local_inv a) = a

-- ============================================================================
-- 7. SHEAVES
-- ============================================================================

def PresheafSection (F : α → Option α) (U : α → Prop) : Prop :=
  ∀ a, U a → ∃ r, F a = some r

theorem restriction_some (F : α → Option α) (res : α → α) (a r : α)
    (h : F a = some r) :
    Option.map res (F a) = some (res r) := by simp [h]

-- ============================================================================
-- 8. SEPARATION AXIOMS
-- ============================================================================

def IsT0 (openα : (α → Prop) → Prop) : Prop :=
  ∀ a b : α, a ≠ b → (∃ U, openα U ∧ U a ∧ ¬U b) ∨ (∃ U, openα U ∧ U b ∧ ¬U a)

def IsT2 (openα : (α → Prop) → Prop) : Prop :=
  ∀ a b : α, a ≠ b →
    ∃ U V, openα U ∧ openα V ∧ U a ∧ V b ∧ ∀ x, ¬(U x ∧ V x)

def IsNormal (openα : (α → Prop) → Prop) : Prop :=
  ∀ (A B : α → Prop), (∀ x, ¬(A x ∧ B x)) →
    ∃ U V, openα U ∧ openα V ∧ (∀ a, A a → U a) ∧ (∀ b, B b → V b) ∧
    ∀ x, ¬(U x ∧ V x)

-- ============================================================================
-- 9. DYNAMICS
-- ============================================================================

def orbit (f : α → α) : Nat → α → α
  | 0, a => a
  | n + 1, a => f (orbit f n a)

def IsFixedPoint (f : α → α) (a : α) : Prop := f a = a
def IsPeriodicPoint (f : α → α) (n : Nat) (a : α) : Prop := orbit f n a = a

def IsErgodic (f : α → α) (inv : (α → Prop) → Prop) : Prop :=
  ∀ S, inv S → (∀ a, S a → S (f a)) → (∀ a, S a) ∨ (∀ a, ¬S a)

-- ============================================================================
-- 10. BAIRE CATEGORY
-- ============================================================================

def IsDense (openα : (α → Prop) → Prop) (D : α → Prop) : Prop :=
  ∀ U, openα U → (∃ a, U a) → ∃ a, U a ∧ D a

def IsBaire (openα : (α → Prop) → Prop) : Prop :=
  ∀ (D : Nat → α → Prop), (∀ n, IsDense openα (D n)) →
    IsDense openα (fun a => ∀ n, D n a)
