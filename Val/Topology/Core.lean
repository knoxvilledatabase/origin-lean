/-
Released under MIT license.
-/
import Val.Algebra

open Classical

/-!
# Topology on Val α: One-Point Compactification

Origin is the point at infinity (limit point of contents).
Container is isolated (discrete extra point).
Contents carry α's topology.

The revelation: "the limit doesn't exist" = "the sequence converges to origin."
The boundary has a name. The field didn't fail; origin was unnamed.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Helpers
-- ============================================================================

/-- Lift a subset of α to a subset of Val α in the contents sort. -/
def liftSet (S : α → Prop) : Val α → Prop
  | contents a => S a
  | _ => False

-- ============================================================================
-- Open Sets: Alexandroff Compactification + Isolated Container
-- ============================================================================

/-- A set U is open if:
    1. Its contents-preimage is open in α.
    2. If origin ∈ U, the complement of that preimage is compact.
    Container membership is unconstrained (isolated). -/
def IsOpen (openα : (α → Prop) → Prop) (compactα : (α → Prop) → Prop)
    (U : Val α → Prop) : Prop :=
  openα (fun a => U (contents a)) ∧
  (U origin → compactα (fun a => ¬ U (contents a)))

-- ============================================================================
-- Container Is Isolated
-- ============================================================================

/-- The singleton {container} is open. -/
theorem container_singleton_open
    (openα : (α → Prop) → Prop) (compactα : (α → Prop) → Prop)
    (h_empty_open : openα (fun _ : α => False)) :
    IsOpen openα compactα (isContainer (α := α)) :=
  ⟨h_empty_open, fun h => h.elim⟩

-- ============================================================================
-- Contents Carry α's Topology
-- ============================================================================

/-- An open set of α lifts to an open set of Val α in the contents sort. -/
theorem contents_open_embedding
    (openα : (α → Prop) → Prop) (compactα : (α → Prop) → Prop)
    (S : α → Prop) (hS : openα S) :
    IsOpen openα compactα (liftSet S) :=
  ⟨hS, fun h => h.elim⟩

-- ============================================================================
-- Origin Is a Limit Point
-- ============================================================================

/-- Every open set containing origin also contains a contents point.
    Requires α to be non-compact — the condition making compactification non-trivial. -/
theorem origin_is_limit_point
    (openα : (α → Prop) → Prop) (compactα : (α → Prop) → Prop)
    (h_noncompact : ∀ K : α → Prop, compactα K → ∃ a : α, ¬ K a)
    (U : Val α → Prop) (hU : IsOpen openα compactα U) (hO : U origin) :
    ∃ a : α, U (contents a) := by
  obtain ⟨_, hcomp⟩ := hU
  obtain ⟨a, ha⟩ := h_noncompact _ (hcomp hO)
  exact ⟨a, byContradiction ha⟩

-- ============================================================================
-- Topological Convergence
-- ============================================================================

/-- Sequence convergence: for every open set containing L, sequence is eventually in it. -/
def topoConverges (openα : (α → Prop) → Prop) (compactα : (α → Prop) → Prop)
    (s : Nat → Val α) (L : Val α) : Prop :=
  ∀ U : Val α → Prop, IsOpen openα compactα U → U L →
    ∃ N : Nat, ∀ n : Nat, N ≤ n → U (s n)

-- ============================================================================
-- Contents Sequences Can Converge to Origin
-- ============================================================================

/-- A contents sequence converges to origin if its values escape every compact set.
    "Going to infinity" = "converging to origin." The limit exists. It's the boundary. -/
theorem contents_can_converge_to_origin
    (openα : (α → Prop) → Prop) (compactα : (α → Prop) → Prop)
    (s : Nat → α)
    (h_escapes : ∀ K : α → Prop, compactα K →
      ∃ N : Nat, ∀ n : Nat, N ≤ n → ¬ K (s n)) :
    topoConverges openα compactα (fun n => contents (s n)) origin := by
  intro U ⟨_, hcomp⟩ hO
  obtain ⟨N, hN⟩ := h_escapes _ (hcomp hO)
  exact ⟨N, fun n hn => byContradiction (hN n hn)⟩

-- ============================================================================
-- Contents Sequences Cannot Converge to Container
-- ============================================================================

/-- No contents sequence converges to container. Container is isolated. -/
theorem contents_cannot_converge_to_container
    (openα : (α → Prop) → Prop) (compactα : (α → Prop) → Prop)
    (h_empty_open : openα (fun _ : α => False))
    (s : Nat → α) (c : α) :
    ¬ topoConverges openα compactα (fun n => contents (s n)) (container c) := by
  intro h
  obtain ⟨N, hN⟩ := h isContainer
    (container_singleton_open openα compactα h_empty_open) trivial
  exact (hN N (Nat.le_refl N)).elim

-- ============================================================================
-- Contents-to-Contents Convergence = α-Convergence
-- ============================================================================

/-- Within contents, the full topology and the subspace agree. -/
theorem contents_to_contents_convergence
    (openα : (α → Prop) → Prop) (compactα : (α → Prop) → Prop)
    (convα : (Nat → α) → α → Prop)
    (hconv : ∀ (s : Nat → α) (L : α), convα s L →
      ∀ S : α → Prop, openα S → S L → ∃ N : Nat, ∀ n : Nat, N ≤ n → S (s n))
    (s : Nat → α) (L : α) (hs : convα s L) :
    topoConverges openα compactα (fun n => contents (s n)) (contents L) := by
  intro U ⟨hopen, _⟩ hL
  exact hconv s L hs (fun a => U (contents a)) hopen hL

end Val
