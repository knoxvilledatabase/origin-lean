/-
Extracted from Logic/IsEmpty/Defs.lean
Genuine: 4 of 21 | Dissolved: 0 | Infrastructure: 17
-/
import Origin.Core

/-!
# Types that are empty

In this file we define a typeclass `IsEmpty`, which expresses that a type has no elements.

## Main declaration

* `IsEmpty`: a typeclass that expresses that a type is empty.
-/

universe u v

variable {α : Sort u} {β : Sort v}

class IsEmpty (α : Sort u) : Prop where
  protected false : α → False

-- INSTANCE (free from Core): Empty.instIsEmpty

-- INSTANCE (free from Core): PEmpty.instIsEmpty

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): Fin.isEmpty

-- INSTANCE (free from Core): Fin.isEmpty'

protected theorem Function.isEmpty [IsEmpty β] (f : α → β) : IsEmpty α :=
  ⟨fun x ↦ IsEmpty.false (f x)⟩

theorem Function.Surjective.isEmpty [IsEmpty α] {f : α → β} (hf : f.Surjective) : IsEmpty β :=
  ⟨fun y ↦ let ⟨x, _⟩ := hf y; IsEmpty.false x⟩

-- INSTANCE (free from Core): {p

-- INSTANCE (free from Core): PProd.isEmpty_left

-- INSTANCE (free from Core): PProd.isEmpty_right

-- INSTANCE (free from Core): Prod.isEmpty_left

-- INSTANCE (free from Core): Prod.isEmpty_right

-- INSTANCE (free from Core): Quot.instIsEmpty

-- INSTANCE (free from Core): Quotient.instIsEmpty

-- INSTANCE (free from Core): [IsEmpty

-- INSTANCE (free from Core): instIsEmptySum

-- INSTANCE (free from Core): [IsEmpty

theorem Subtype.isEmpty_of_false {p : α → Prop} (hp : ∀ a, ¬p a) : IsEmpty (Subtype p) :=
  ⟨fun x ↦ hp _ x.2⟩

-- INSTANCE (free from Core): Subtype.isEmpty_false

-- INSTANCE (free from Core): Sigma.isEmpty_left

example [h : Nonempty α] [IsEmpty β] : IsEmpty (α → β) := by infer_instance
