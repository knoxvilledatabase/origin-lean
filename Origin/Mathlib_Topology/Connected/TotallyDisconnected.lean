/-
Extracted from Topology/Connected/TotallyDisconnected.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Totally disconnected and totally separated topological spaces

## Main definitions
We define the following properties for sets in a topological space:

* `IsTotallyDisconnected`: all of its connected components are singletons.
* `IsTotallySeparated`: any two points can be separated by two disjoint opens that cover the set.

For both of these definitions, we also have a class stating that the whole space
satisfies that property: `TotallyDisconnectedSpace`, `TotallySeparatedSpace`.
-/

open Function Set Topology

universe u v

variable {α : Type u} {β : Type v} {ι : Type*} {X : ι → Type*} [TopologicalSpace α]
  {s t u v : Set α}

section TotallyDisconnected

def IsTotallyDisconnected (s : Set α) : Prop :=
  ∀ t, t ⊆ s → IsPreconnected t → t.Subsingleton

theorem isTotallyDisconnected_empty : IsTotallyDisconnected (∅ : Set α) := fun _ ht _ _ x_in _ _ =>
  (ht x_in).elim

theorem isTotallyDisconnected_singleton {x} : IsTotallyDisconnected ({x} : Set α) := fun _ ht _ =>
  subsingleton_singleton.anti ht
