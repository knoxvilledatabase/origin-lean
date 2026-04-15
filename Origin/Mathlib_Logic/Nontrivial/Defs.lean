/-
Extracted from Logic/Nontrivial/Defs.lean
Genuine: 10 of 13 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Nontrivial types

A type is *nontrivial* if it contains at least two elements. This is useful in particular for rings
(where it is equivalent to the fact that zero is different from one) and for vector spaces
(where it is equivalent to the fact that the dimension is positive).

We introduce a typeclass `Nontrivial` formalizing this property.

Basic results about nontrivial types are in `Mathlib/Logic/Nontrivial/Basic.lean`.
-/

variable {α : Type*} {β : Type*}

class Nontrivial (α : Type*) : Prop where
  /-- In a nontrivial type, there exists a pair of distinct terms. -/
  exists_pair_ne : ∃ x y : α, x ≠ y

theorem nontrivial_iff : Nontrivial α ↔ ∃ x y : α, x ≠ y :=
  ⟨fun h ↦ h.exists_pair_ne, fun h ↦ ⟨h⟩⟩

theorem exists_pair_ne (α : Type*) [Nontrivial α] : ∃ x y : α, x ≠ y :=
  Nontrivial.exists_pair_ne

protected theorem Function.Injective.nontrivial [Nontrivial α] {f : α → β}
    (hf : Function.Injective f) : Nontrivial β :=
  let ⟨x, y, h⟩ := exists_pair_ne α
  ⟨⟨f x, f y, hf.ne h⟩⟩

protected theorem Function.Injective.exists_ne [Nontrivial α] {f : α → β}
    (hf : Function.Injective f) (y : β) : ∃ x, f x ≠ y := by
  rcases exists_pair_ne α with ⟨x₁, x₂, hx⟩
  by_cases h : f x₂ = y
  · exact ⟨x₁, (hf.ne_iff' h).2 hx⟩
  · exact ⟨x₂, h⟩

protected theorem Decidable.exists_ne [Nontrivial α] [DecidableEq α] (x : α) : ∃ y, y ≠ x := by
  rcases exists_pair_ne α with ⟨y, y', h⟩
  by_cases hx : x = y
  · rw [← hx] at h
    exact ⟨y', h.symm⟩
  · exact ⟨y, Ne.symm hx⟩

open Classical in

theorem exists_ne [Nontrivial α] (x : α) : ∃ y, y ≠ x := Decidable.exists_ne x

theorem nontrivial_of_ne (x y : α) (h : x ≠ y) : Nontrivial α :=
  ⟨⟨x, y, h⟩⟩

theorem nontrivial_iff_exists_ne (x : α) : Nontrivial α ↔ ∃ y, y ≠ x :=
  ⟨fun h ↦ @exists_ne α h x, fun ⟨_, hy⟩ ↦ nontrivial_of_ne _ _ hy⟩

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): (priority

theorem subsingleton_iff : Subsingleton α ↔ ∀ x y : α, x = y :=
  ⟨by
    intro h
    exact Subsingleton.elim, fun h ↦ ⟨h⟩⟩
