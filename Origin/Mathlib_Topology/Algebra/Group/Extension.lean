/-
Extracted from Topology/Algebra/Group/Extension.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Short exact sequences of topological groups

In this file, we define a short exact sequence of topological groups to be a closed embedding `φ`
followed by an open quotient map `ψ` satisfying `φ.range = ψ.ker`.

## Main definitions

* `TopologicalGroup.IsSES φ ψ`: A predicate stating that `φ` is a closed embedding, `ψ` is an open
  quotient map, and `φ.range = ψ.ker`.

-/

open scoped Pointwise

structure TopologicalGroup.IsSES {A B C : Type*} [Group A] [Group B] [Group C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] (φ : A →* B) (ψ : B →* C) where
  isClosedEmbedding : Topology.IsClosedEmbedding φ
  isOpenQuotientMap : IsOpenQuotientMap ψ
  mulExact : Function.MulExact φ ψ

structure TopologicalAddGroup.IsSES {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] (φ : A →+ B) (ψ : B →+ C) where
  isClosedEmbedding : Topology.IsClosedEmbedding φ
  isOpenQuotientMap : IsOpenQuotientMap ψ
  exact : Function.Exact φ ψ

attribute [to_additive TopologicalAddGroup.IsSES] TopologicalGroup.IsSES

namespace TopologicalGroup.IsSES
