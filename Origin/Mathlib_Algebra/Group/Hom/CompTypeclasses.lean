/-
Extracted from Algebra/Group/Hom/CompTypeclasses.lean
Genuine: 5 of 11 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Propositional typeclasses on several monoid homs

This file contains typeclasses used in the definition of equivariant maps,
in the spirit what was initially developed by Frédéric Dupuis and Heather Macbeth for linear maps.
However, we do not expect that all maps should be guessed automatically,
as it happens for linear maps.

If `φ`, `ψ`… are monoid homs and `M`, `N`… are monoids, we add two instances:
* `MonoidHom.CompTriple φ ψ χ`, which expresses that `ψ.comp φ = χ`
* `MonoidHom.IsId φ`, which expresses that `φ = id`

Some basic lemmas are proved:
* `MonoidHom.CompTriple.comp` asserts `MonoidHom.CompTriple φ ψ (ψ.comp φ)`
* `MonoidHom.CompTriple.id_comp` asserts `MonoidHom.CompTriple φ ψ ψ`
  in the presence of `MonoidHom.IsId φ`
* its variant `MonoidHom.CompTriple.comp_id`

TODO :
* align with RingHomCompTriple
* probably rename MonoidHom.CompTriple as MonoidHomCompTriple
  (or, on the opposite, rename RingHomCompTriple as RingHom.CompTriple)
* does one need AddHom.CompTriple ?

-/

section MonoidHomCompTriple

namespace MonoidHom

class CompTriple {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]
    (φ : M →* N) (ψ : N →* P) (χ : outParam (M →* P)) : Prop where
  /-- The maps form a commuting triangle -/
  comp_eq : ψ.comp φ = χ

attribute [simp] CompTriple.comp_eq

namespace CompTriple

variable {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]

class IsId (σ : M →* M) : Prop where
  eq_id : σ = MonoidHom.id M

-- INSTANCE (free from Core): instIsId

-- INSTANCE (free from Core): {σ

-- INSTANCE (free from Core): instComp_id

-- INSTANCE (free from Core): instId_comp

lemma comp_inv {φ : M →* N} {ψ : N →* M} (h : Function.RightInverse φ ψ)
    {χ : M →* M} [IsId χ] :
    CompTriple φ ψ χ where
  comp_eq := by simp only [IsId.eq_id, ← DFunLike.coe_fn_eq, coe_comp, h.id, coe_id]

-- INSTANCE (free from Core): instRootCompTriple

lemma comp_apply
    {φ : M →* N} {ψ : N →* P} {χ : M →* P} (h : CompTriple φ ψ χ) (x : M) :
    ψ (φ x) = χ x := by
  rw [← h.comp_eq, MonoidHom.comp_apply]

theorem comp_assoc {Q : Type*} [Monoid Q]
    {φ₁ : M →* N} {φ₂ : N →* P} {φ₁₂ : M →* P}
    (κ : CompTriple φ₁ φ₂ φ₁₂)
    {φ₃ : P →* Q} {φ₂₃ : N →* Q} (κ' : CompTriple φ₂ φ₃ φ₂₃)
    {φ₁₂₃ : M →* Q} :
    CompTriple φ₁ φ₂₃ φ₁₂₃ ↔ CompTriple φ₁₂ φ₃ φ₁₂₃ := by
  constructor <;>
  · rintro ⟨h⟩
    exact ⟨by simp only [← κ.comp_eq, ← h, ← κ'.comp_eq, MonoidHom.comp_assoc]⟩

end MonoidHom.CompTriple

end MonoidHomCompTriple
