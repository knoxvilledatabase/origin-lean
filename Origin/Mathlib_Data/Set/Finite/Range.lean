/-
Extracted from Data/Set/Finite/Range.lean
Genuine: 3 of 6 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Finiteness of `Set.range`

## Implementation notes

Each result in this file should come in three forms: a `Fintype` instance, a `Finite` instance
and a `Set.Finite` constructor.

## Tags

finite sets
-/

assert_not_exists IsOrderedRing MonoidWithZero

open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Set

/-! ### Fintype instances

Every instance here should have a corresponding `Set.Finite` constructor in the next section.
-/

section FintypeInstances

-- INSTANCE (free from Core): fintypeRange

end FintypeInstances

end Set

/-! ### Finite instances

There is seemingly some overlap between the following instances and the `Fintype` instances
in `Data.Set.Finite`. While every `Fintype` instance gives a `Finite` instance, those
instances that depend on `Fintype` or `Decidable` instances need an additional `Finite` instance
to be able to generally apply.

Some set instances do not appear here since they are consequences of others, for example
`Subtype.Finite` for subsets of a finite type.
-/

namespace Finite.Set

-- INSTANCE (free from Core): finite_range

-- INSTANCE (free from Core): finite_replacement

end Finite.Set

namespace Set

/-! ### Constructors for `Set.Finite`

Every constructor here should have a corresponding `Fintype` instance in the previous section
(or in the `Fintype` module).

The implementation of these constructors ideally should be no more than `Set.toFinite`,
after possibly setting up some `Fintype` and classical `Decidable` instances.
-/

section SetFiniteConstructors

theorem finite_range (f : ι → α) [Finite ι] : (range f).Finite :=
  toFinite _

theorem Finite.dependent_image {s : Set α} (hs : s.Finite) (F : ∀ i ∈ s, β) :
    {y : β | ∃ x hx, F x hx = y}.Finite := by
  have := hs.to_subtype
  simpa [range] using finite_range fun x : s => F x x.2

end SetFiniteConstructors

lemma Finite.exists_subset_finite_image_eq {f : α → β} {s : Set α} {u : Set β}
    (hu : u.Finite) (hsu : u ⊆ f '' s) :
    ∃ᵉ (t ⊆ s) (_ : t.Finite), f '' t = u := by
  have : Finite u := Finite.to_subtype hu
  choose g hg hg' using hsu
  let g' (x : u) : α := g x.property
  exact ⟨range g', fun a ha ↦ by aesop, finite_range _, by aesop⟩

end Set
