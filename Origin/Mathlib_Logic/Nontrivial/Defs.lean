/-
Extracted from Logic/Nontrivial/Defs.lean
Genuine: 1 | Conflates: 14 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.Logic.Function.Defs
import Mathlib.Tactic.TypeStar

noncomputable section

/-!
# Nontrivial types

A type is *nontrivial* if it contains at least two elements. This is useful in particular for rings
(where it is equivalent to the fact that zero is different from one) and for vector spaces
(where it is equivalent to the fact that the dimension is positive).

We introduce a typeclass `Nontrivial` formalizing this property.

Basic results about nontrivial types are in `Mathlib.Logic.Nontrivial.Basic`.
-/

variable {α : Type*} {β : Type*}

-- CONFLATES (assumes ground = zero): Nontrivial
class Nontrivial (α : Type*) : Prop where
  /-- In a nontrivial type, there exists a pair of distinct terms. -/
  exists_pair_ne : ∃ x y : α, x ≠ y

-- CONFLATES (assumes ground = zero): nontrivial_iff
theorem nontrivial_iff : Nontrivial α ↔ ∃ x y : α, x ≠ y :=
  ⟨fun h ↦ h.exists_pair_ne, fun h ↦ ⟨h⟩⟩

-- CONFLATES (assumes ground = zero): exists_pair_ne
theorem exists_pair_ne (α : Type*) [Nontrivial α] : ∃ x y : α, x ≠ y :=
  Nontrivial.exists_pair_ne

-- CONFLATES (assumes ground = zero): Decidable.exists_ne
protected theorem Decidable.exists_ne [Nontrivial α] [DecidableEq α] (x : α) : ∃ y, y ≠ x := by
  rcases exists_pair_ne α with ⟨y, y', h⟩
  by_cases hx : x = y
  · rw [← hx] at h
    exact ⟨y', h.symm⟩
  · exact ⟨y, Ne.symm hx⟩

open Classical in

-- CONFLATES (assumes ground = zero): exists_ne
theorem exists_ne [Nontrivial α] (x : α) : ∃ y, y ≠ x := Decidable.exists_ne x

-- CONFLATES (assumes ground = zero): nontrivial_of_ne
theorem nontrivial_of_ne (x y : α) (h : x ≠ y) : Nontrivial α :=
  ⟨⟨x, y, h⟩⟩

-- CONFLATES (assumes ground = zero): nontrivial_iff_exists_ne
theorem nontrivial_iff_exists_ne (x : α) : Nontrivial α ↔ ∃ y, y ≠ x :=
  ⟨fun h ↦ @exists_ne α h x, fun ⟨_, hy⟩ ↦ nontrivial_of_ne _ _ hy⟩

instance : Nontrivial Prop :=
  ⟨⟨True, False, true_ne_false⟩⟩

instance (priority := 500) Nontrivial.to_nonempty [Nontrivial α] : Nonempty α :=
  let ⟨x, _⟩ := _root_.exists_pair_ne α
  ⟨x⟩

theorem subsingleton_iff : Subsingleton α ↔ ∀ x y : α, x = y :=
  ⟨by
    intro h
    exact Subsingleton.elim, fun h ↦ ⟨h⟩⟩

-- CONFLATES (assumes ground = zero): not_nontrivial_iff_subsingleton
theorem not_nontrivial_iff_subsingleton : ¬Nontrivial α ↔ Subsingleton α := by
  simp only [nontrivial_iff, subsingleton_iff, not_exists, Classical.not_not]

-- CONFLATES (assumes ground = zero): not_nontrivial
theorem not_nontrivial (α) [Subsingleton α] : ¬Nontrivial α :=
  fun ⟨⟨x, y, h⟩⟩ ↦ h <| Subsingleton.elim x y

-- CONFLATES (assumes ground = zero): not_subsingleton
theorem not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α :=
  fun _ => not_nontrivial _ ‹_›

-- CONFLATES (assumes ground = zero): not_subsingleton_iff_nontrivial
lemma not_subsingleton_iff_nontrivial : ¬ Subsingleton α ↔ Nontrivial α := by
  rw [← not_nontrivial_iff_subsingleton, Classical.not_not]

-- CONFLATES (assumes ground = zero): subsingleton_or_nontrivial
theorem subsingleton_or_nontrivial (α : Type*) : Subsingleton α ∨ Nontrivial α := by
  rw [← not_nontrivial_iff_subsingleton, or_comm]
  exact Classical.em _

-- CONFLATES (assumes ground = zero): false_of_nontrivial_of_subsingleton
theorem false_of_nontrivial_of_subsingleton (α : Type*) [Nontrivial α] [Subsingleton α] : False :=
  not_nontrivial _ ‹_›

-- CONFLATES (assumes ground = zero): Function.Surjective.nontrivial
protected theorem Function.Surjective.nontrivial [Nontrivial β] {f : α → β}
    (hf : Function.Surjective f) : Nontrivial α := by
  rcases exists_pair_ne β with ⟨x, y, h⟩
  rcases hf x with ⟨x', hx'⟩
  rcases hf y with ⟨y', hy'⟩
  have : x' ≠ y' := by
    refine fun H ↦ h ?_
    rw [← hx', ← hy', H]
  exact ⟨⟨x', y', this⟩⟩

namespace Bool

instance : Nontrivial Bool :=
  ⟨⟨true, false, nofun⟩⟩

end Bool
