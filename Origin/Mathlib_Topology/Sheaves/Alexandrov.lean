/-
Extracted from Topology/Sheaves/Alexandrov.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

Let `X` be a preorder `≤`, and consider the associated Alexandrov topology on `X`.
Given a functor `F : X ⥤ C` to a complete category, we can extend `F` to a
presheaf on (the topological space) `X` by taking the right Kan extension along the canonical
functor `X ⥤ (Opens X)ᵒᵖ` sending `x : X` to the principal open `{y | x ≤ y}` in the
Alexandrov topology.

This file proves that this presheaf is a sheaf.

-/

noncomputable section

universe v u

open CategoryTheory Limits Functor

open TopCat Presheaf SheafCondition

open TopologicalSpace Topology

variable
  {X : Type v} [TopologicalSpace X] [Preorder X] [Topology.IsUpperSet X]
  {C : Type u} [Category.{v} C] [HasLimits C]
  (F : X ⥤ C)

namespace Alexandrov

def principalOpen (x : X) : Opens X := .mk { y | x ≤ y } <| by
  rw [IsUpperSet.isOpen_iff_isUpperSet]
  intro y z h1 h2
  exact le_trans h2 h1

lemma self_mem_principalOpen (x : X) : x ∈ principalOpen x := le_refl _
