/-
Extracted from Logic/Function/CompTypeclasses.lean
Genuine: 4 of 8 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Propositional typeclasses on several maps

This file contains typeclasses that are used in the definition of
equivariant maps in the spirit what was initially developed
by Frédéric Dupuis and Heather Macbeth for linear maps.

* `CompTriple φ ψ χ`, which expresses that `ψ.comp φ = χ`
* `CompTriple.IsId φ`, which expresses that `φ = id`

TODO :
* align with RingHomCompTriple

-/

section CompTriple

class CompTriple {M N P : Type*} (φ : M → N) (ψ : N → P) (χ : outParam (M → P)) : Prop where
  /-- The maps form a commuting triangle -/
  comp_eq : ψ.comp φ = χ

attribute [simp] CompTriple.comp_eq

namespace CompTriple

class IsId {M : Type*} (σ : M → M) : Prop where
  eq_id : σ = id

-- INSTANCE (free from Core): {M

-- INSTANCE (free from Core): instComp_id

-- INSTANCE (free from Core): instId_comp

lemma comp_inv {M N : Type*} {φ : M → N} {ψ : N → M}
    (h : Function.RightInverse φ ψ) {χ : M → M} [IsId χ] :
    CompTriple φ ψ χ where
  comp_eq := by simp only [IsId.eq_id, h.id]

lemma comp_apply {M N P : Type*}
    {φ : M → N} {ψ : N → P} {χ : M → P} (h : CompTriple φ ψ χ) (x : M) :
    ψ (φ x) = χ x := by
  rw [← h.comp_eq, Function.comp_apply]

end CompTriple

end CompTriple
