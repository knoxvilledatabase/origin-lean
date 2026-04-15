/-
Extracted from Dynamics/Transitive.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Topologically transitive monoid actions

In this file we define an action of a monoid `M` on a topological space `α` to be
*topologically transitive* if for any pair of nonempty open sets `U` and `V` in `α` there exists an
`m : M` such that `(m • U) ∩ V` is nonempty. We also provide an additive version of this definition
and prove basic facts about topologically transitive actions.

## Tags

group action, topologically transitive
-/

open scoped Pointwise

class AddAction.IsTopologicallyTransitive (M α : Type*) [AddMonoid M] [TopologicalSpace α]
    [AddAction M α] : Prop where
  exists_vadd_inter : ∀ {U V : Set α}, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
    ∃ m : M, ((m +ᵥ U) ∩ V).Nonempty
