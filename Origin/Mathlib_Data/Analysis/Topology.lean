/-
Extracted from Data/Analysis/Topology.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Computational realization of topological spaces (experimental)

This file provides infrastructure to compute with topological spaces.

## Main declarations

* `Ctop`: Realization of a topology basis.
* `Ctop.Realizer`: Realization of a topological space. `Ctop` that generates the given topology.
* `LocallyFinite.Realizer`: Realization of the local finiteness of an indexed family of sets.
* `Compact.Realizer`: Realization of the compactness of a set.
-/

open Set

open Filter hiding Realizer

open Topology

structure Ctop (α σ : Type*) where
  f : σ → Set α
  top : α → σ
  top_mem : ∀ x : α, x ∈ f (top x)
  inter : ∀ (a b) (x : α), x ∈ f a ∩ f b → σ
  inter_mem : ∀ a b x h, x ∈ f (inter a b x h)
  inter_sub : ∀ a b x h, f (inter a b x h) ⊆ f a ∩ f b

variable {α : Type*} {β : Type*} {σ : Type*} {τ : Type*}

-- INSTANCE (free from Core): :

namespace Ctop

variable (F : Ctop α σ)

-- INSTANCE (free from Core): :

def ofEquiv (E : σ ≃ τ) : Ctop α σ → Ctop α τ
  | ⟨f, T, h₁, I, h₂, h₃⟩ =>
    { f := fun a ↦ f (E.symm a)
      top := fun x ↦ E (T x)
      top_mem := fun x ↦ by simpa using h₁ x
      inter := fun a b x h ↦ E (I (E.symm a) (E.symm b) x h)
      inter_mem := fun a b x h ↦ by simpa using h₂ (E.symm a) (E.symm b) x h
      inter_sub := fun a b x h ↦ by simpa using h₃ (E.symm a) (E.symm b) x h }
