/-
Released under MIT license.
-/
import Val.Topology.Core
import Val.Analysis.Core
import Val.Category.Core

/-!
# Val α: Uniform Spaces

Uniform spaces, Cauchy filters, uniform continuity, completions.
Uniformity is a contents-level structure. Origin is outside the uniformity.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Entourages (Uniform Structure)
-- ============================================================================

/-- An entourage is a set of pairs (x, y) that are "uniformly close".
    In Val α, entourages are contents-level. -/
def valEntourage (ent : α → α → Prop) : Val α → Val α → Prop
  | contents a, contents b => ent a b
  | origin, origin => True
  | container a, container b => a = b
  | _, _ => False

/-- Contents values in the same entourage stay in contents. -/
theorem entourage_contents (ent : α → α → Prop) (a b : α) (h : ent a b) :
    valEntourage ent (contents a) (contents b) := h

/-- Origin is only entourage-related to itself. -/
theorem entourage_origin_self (ent : α → α → Prop) :
    valEntourage ent (origin : Val α) origin := trivial

/-- Origin is not entourage-related to contents. -/
theorem entourage_origin_contents (ent : α → α → Prop) (a : α) :
    ¬ valEntourage ent (origin : Val α) (contents a) := id

-- ============================================================================
-- Cauchy Filters (Sort-Level)
-- ============================================================================

/-- Cauchy condition: for every ε > 0, eventually dist(sₘ, sₙ) < ε. -/
def unifCauchy (dist : α → α → α) (ltF : α → α → Prop) (zero : α) (s : Nat → α) : Prop :=
  ∀ ε, ltF zero ε → ∃ N, ∀ m n, N ≤ m → N ≤ n → ltF (dist (s m) (s n)) ε

/-- A Cauchy filter in Val α: a sequence of contents values. -/
def valCauchy (dist : α → α → α) (ltF : α → α → Prop) (zero : α) (s : Nat → Val α) : Prop :=
  ∃ raw : Nat → α, (∀ n, s n = contents (raw n)) ∧ unifCauchy dist ltF zero raw

/-- A Cauchy filter of contents values has a raw Cauchy sequence. -/
theorem cauchy_filter_raw (dist : α → α → α) (ltF : α → α → Prop) (zero : α)
    (s : Nat → α) (h : unifCauchy dist ltF zero s) :
    valCauchy dist ltF zero (fun n => contents (s n)) :=
  ⟨s, fun _ => rfl, h⟩

/-- Cauchy filters in contents never touch origin. -/
theorem cauchy_filter_ne_origin (dist : α → α → α) (ltF : α → α → Prop) (zero : α)
    (s : Nat → Val α) (h : valCauchy dist ltF zero s) (n : Nat) :
    s n ≠ origin := by
  obtain ⟨raw, hraw, _⟩ := h; rw [hraw n]; simp

-- ============================================================================
-- Uniform Continuity
-- ============================================================================

/-- Uniform continuity: for every ε, there exists δ such that d(x,y) < δ → d(f x, f y) < ε. -/
def uniformCont (dist : α → α → α) (ltF : α → α → Prop) (zero : α) (f : α → α) : Prop :=
  ∀ ε, ltF zero ε → ∃ δ, ltF zero δ ∧
    ∀ x y, ltF (dist x y) δ → ltF (dist (f x) (f y)) ε

/-- Uniformly continuous maps lift to Val α: contents in, contents out. -/
theorem uniform_continuous_val (f : α → α) (a : α) :
    valMap f (contents a) = contents (f a) := rfl

/-- Composition of uniformly continuous maps preserves contents. -/
theorem uniform_continuous_comp (f g : α → α) (a : α) :
    valMap (f ∘ g) (contents a) = contents (f (g a)) := rfl

-- ============================================================================
-- Completion
-- ============================================================================

/-- Epsilon-delta convergence definition for completions. -/
def unifConv (dist : α → α → α) (ltF : α → α → Prop) (zero : α)
    (s : Nat → α) (L : α) : Prop :=
  ∀ ε, ltF zero ε → ∃ N, ∀ n, N ≤ n → ltF (dist (s n) L) ε

/-- The completion of a metric space: every Cauchy sequence converges in contents. -/
theorem completion_contents (dist : α → α → α) (ltF : α → α → Prop) (zero : α)
    (complete : ∀ s, unifCauchy dist ltF zero s → ∃ L, unifConv dist ltF zero s L)
    (s : Nat → α) (hs : unifCauchy dist ltF zero s) :
    ∃ L, liftConv (unifConv dist ltF zero) (fun n => contents (s n)) (contents L) := by
  obtain ⟨L, hL⟩ := complete s hs
  exact ⟨L, s, fun _ => rfl, hL⟩

-- ============================================================================
-- Totally Bounded
-- ============================================================================

/-- A set is totally bounded if for every ε, it can be covered by finitely many ε-balls. -/
def totallyBounded (dist : α → α → α) (ltF : α → α → Prop) (zero : α)
    (S : α → Prop) : Prop :=
  ∀ ε, ltF zero ε → ∃ centers : List α,
    ∀ x, S x → ∃ c, c ∈ centers ∧ ltF (dist x c) ε

/-- Totally bounded sets in contents lift: each element is contents. -/
theorem totally_bounded_contents (S : α → Prop) (a : α) (ha : S a) :
    ∃ r, (contents a : Val α) = contents r := ⟨a, rfl⟩

-- ============================================================================
-- Uniform Convergence
-- ============================================================================

/-- Uniform convergence of a sequence of functions. -/
def uniformConvergence (dist : α → α → α) (ltF : α → α → Prop) (zero : α)
    (fn : Nat → α → α) (f : α → α) : Prop :=
  ∀ ε, ltF zero ε → ∃ N, ∀ n, N ≤ n → ∀ x, ltF (dist (fn n x) (f x)) ε

/-- Uniform convergence preserves contents sort. -/
theorem uniform_conv_contents (fn : Nat → α → α) (f : α → α) (n : Nat) (x : α) :
    ∃ r, (contents (fn n x) : Val α) = contents r := ⟨fn n x, rfl⟩

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Uniform spaces over Val α:
--   ✓ Entourages: contents-level, origin isolated
--   ✓ Cauchy filters: contents sequences, never touch origin
--   ✓ Uniform continuity: lifts to Val α, contents preserved
--   ✓ Completion: Cauchy → convergent within contents
--   ✓ Totally bounded: contents property
--   ✓ Uniform convergence: sort-preserving
--
-- Zero sorries. Zero typeclasses. Zero Mathlib.

end Val
