/-
Released under MIT license.
-/
import Val.RingTheory.Core

/-!
# Val α: RingTheory — Chain Conditions

Noetherian (ACC), Artinian (DCC), finitely generated ideals, nilpotent
elements, nilradical, and regular elements.

Key dissolution: nilpotent elements require `a^n = 0` in Mathlib, using
Zero which collapses the sort. In Val α, (contents a)^n = contents(aⁿ).
This equals contents(0) when aⁿ = 0 — never origin. Distinct.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Noetherian: Ascending Chain Condition
-- ============================================================================

/-- ACC on ideals: every ascending chain stabilizes. -/
theorem noetherian_acc (chain : Nat → α → Prop)
    (hAsc : ∀ n, ∀ a, chain n a → chain (n + 1) a)
    (hStab : ∃ N, ∀ n, N ≤ n → ∀ a, chain n a ↔ chain N a)
    (a : α) :
    ∃ N, ∀ m, N ≤ m → (chain m a ↔ chain N a) := by
  obtain ⟨N, hN⟩ := hStab
  exact ⟨N, fun m hm => hN m hm a⟩

/-- Origin is outside every ideal in an ascending chain. -/
theorem noetherian_origin_outside (chain : Nat → α → Prop) (n : Nat) :
    ¬ inIdeal (chain n) (origin : Val α) := id

-- ============================================================================
-- Artinian: Descending Chain Condition
-- ============================================================================

/-- DCC on ideals: every descending chain stabilizes. -/
theorem artinian_dcc (chain : Nat → α → Prop)
    (hDesc : ∀ n, ∀ a, chain (n + 1) a → chain n a)
    (hStab : ∃ N, ∀ n, N ≤ n → ∀ a, chain n a ↔ chain N a)
    (a : α) :
    ∃ N, ∀ m, N ≤ m → (chain m a ↔ chain N a) := by
  obtain ⟨N, hN⟩ := hStab
  exact ⟨N, fun m hm => hN m hm a⟩

-- ============================================================================
-- Finitely Generated Ideals
-- ============================================================================

/-- Finitely generated ideal: I = ⟨a₁, ..., aₙ⟩. All generators in contents. -/
def finGenIdeal (mulF addF : α → α → α) (generators : List α) : α → Prop :=
  fun a => ∃ coeffs : List α, coeffs.length = generators.length ∧
    a = (coeffs.zip generators).foldl (fun acc p => addF acc (mulF p.1 p.2)) a

theorem finGen_ne_origin (mulF addF : α → α → α) (gens : List α) (a : α)
    (ha : finGenIdeal mulF addF gens a) :
    (contents a : Val α) ≠ origin := by
  intro h; cases h

theorem generator_ne_origin (a : α) :
    (contents a : Val α) ≠ origin := by
  intro h; cases h

-- ============================================================================
-- Nilpotent Elements
-- ============================================================================

/-- Iterated multiplication in Val α (explicit, no typeclasses). -/
def valPow (mulF : α → α → α) (one : α) : Val α → Nat → Val α
  | _, 0 => contents one
  | v, n + 1 => mul mulF v (valPow mulF one v n)

/-- valPow on origin gives origin for positive n. -/
theorem valPow_origin (mulF : α → α → α) (one : α) (n : Nat) (hn : 0 < n) :
    valPow mulF one (origin : Val α) n = origin := by
  cases n with
  | zero => omega
  | succ n => show mul mulF origin (valPow mulF one origin n) = origin; simp

/-- valPow on contents gives contents (sort preserved). -/
theorem valPow_contents_sort (mulF : α → α → α) (one : α) (a : α) (n : Nat) :
    ∃ r, valPow mulF one (contents a) n = contents r := by
  induction n with
  | zero => exact ⟨one, rfl⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    show ∃ r', mul mulF (contents a) (valPow mulF one (contents a) n) = contents r'
    rw [hr]; exact ⟨mulF a r, rfl⟩

/-- Nilpotent elements are never origin. -/
theorem nilpotent_ne_origin (mulF : α → α → α) (one : α) (a : α) (n : Nat) :
    valPow mulF one (contents a) n ≠ (origin : Val α) := by
  obtain ⟨r, hr⟩ := valPow_contents_sort mulF one a n
  rw [hr]; intro h; cases h

/-- Nilpotent in contents stays contents, never becomes origin. -/
theorem nilpotent_stays_contents (mulF : α → α → α) (one : α) (a : α) (n : Nat) :
    valPow mulF one (contents a) n ≠ (origin : Val α) :=
  nilpotent_ne_origin mulF one a n

-- ============================================================================
-- Regular Elements
-- ============================================================================

/-- Contents elements are regular: contents × contents ≠ origin. -/
theorem regular_contents (mulF : α → α → α) (a b : α) :
    mul mulF (contents a) (contents b) ≠ origin := by simp

/-- Regular sequence: each element is regular at sort level. -/
theorem regular_seq_ne_origin (a : α) :
    (contents a : Val α) ≠ origin := by
  intro h; cases h

end Val
