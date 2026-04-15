/-
Extracted from Order/Filter/Ultrafilter/Defs.lean
Genuine: 3 of 7 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Ultrafilters

An ultrafilter is a minimal (maximal in the set order) proper filter.
In this file we define

* `Ultrafilter.of`: an ultrafilter that is less than or equal to a given filter;
* `Ultrafilter`: subtype of ultrafilters;
* `pure x : Ultrafilter α`: `pure x` as an `Ultrafilter`;
* `Ultrafilter.map`, `Ultrafilter.bind`, `Ultrafilter.comap` : operations on ultrafilters;
-/

assert_not_exists Set.Finite

universe u v

variable {α : Type u} {β : Type v} {γ : Type*}

open Set Filter Function

-- INSTANCE (free from Core): :

structure Ultrafilter (α : Type*) extends Filter α where
  /-- An ultrafilter is nontrivial. -/
  protected neBot' : NeBot toFilter
  /-- If `g` is a nontrivial filter that is less than or equal to an ultrafilter, then it is greater
  than or equal to the ultrafilter. -/
  protected le_of_le : ∀ g, Filter.NeBot g → g ≤ toFilter → toFilter ≤ g

namespace Ultrafilter

variable {f g : Ultrafilter α} {s t : Set α} {p q : α → Prop}

attribute [coe] Ultrafilter.toFilter

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

theorem unique (f : Ultrafilter α) {g : Filter α} (h : g ≤ f) (hne : NeBot g := by infer_instance) :
    g = f :=
  le_antisymm h <| f.le_of_le g hne h

-- INSTANCE (free from Core): neBot

protected theorem isAtom (f : Ultrafilter α) : IsAtom (f : Filter α) :=
  ⟨f.neBot.ne, fun _ hgf => by_contra fun hg => hgf.ne <| f.unique hgf.le ⟨hg⟩⟩
