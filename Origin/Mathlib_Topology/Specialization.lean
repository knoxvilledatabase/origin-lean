/-
Extracted from Topology/Specialization.lean
Genuine: 11 | Conflates: 0 | Dissolved: 0 | Infrastructure: 11
-/
import Origin.Core
import Mathlib.Order.Category.Preord
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order.UpperLowerSetTopology

noncomputable section

/-!
# Specialization order

This file defines a type synonym for a topological space considered with its specialisation order.
-/

open CategoryTheory Topology

def Specialization (α : Type*) := α

namespace Specialization

variable {α β γ : Type*}

@[match_pattern] def toEquiv : α ≃ Specialization α := Equiv.refl _

@[match_pattern] def ofEquiv : Specialization α ≃ α := Equiv.refl _

@[simp, nolint simpNF] lemma ofEquiv_inj {a b : Specialization α} : ofEquiv a = ofEquiv b ↔ a = b :=

Iff.rfl

@[elab_as_elim, cases_eliminator, induction_eliminator]
protected def rec {β : Specialization α → Sort*} (h : ∀ a, β (toEquiv a)) (a : Specialization α) :
    β a :=
  h (ofEquiv a)

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

instance instPreorder : Preorder (Specialization α) := specializationPreorder α

instance instPartialOrder [T0Space α] : PartialOrder (Specialization α) := specializationOrder α

@[simp] lemma isOpen_toEquiv_preimage [AlexandrovDiscrete α] {s : Set (Specialization α)} :
  IsOpen (toEquiv ⁻¹' s) ↔ IsUpperSet s := isOpen_iff_forall_specializes.trans forall_swap

@[simp] lemma isUpperSet_ofEquiv_preimage [AlexandrovDiscrete α] {s : Set α} :
  IsUpperSet (ofEquiv ⁻¹' s) ↔ IsOpen s := isOpen_toEquiv_preimage.symm

def map (f : C(α, β)) : Specialization α →o Specialization β where
  toFun := toEquiv ∘ f ∘ ofEquiv
  monotone' := (map_continuous f).specialization_monotone

end Specialization

open Set Specialization WithUpperSet

def homeoWithUpperSetTopologyorderIso (α : Type*) [TopologicalSpace α] [AlexandrovDiscrete α] :
    α ≃ₜ WithUpperSet (Specialization α) :=
  (toEquiv.trans toUpperSet).toHomeomorph fun s ↦ by simp [Set.preimage_comp]

@[simps]
def topToPreord : TopCat ⥤ Preord where
  obj X := Preord.of <| Specialization X
  map := Specialization.map
