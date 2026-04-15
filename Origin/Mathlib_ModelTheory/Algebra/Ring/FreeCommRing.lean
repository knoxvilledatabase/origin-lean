/-
Extracted from ModelTheory/Algebra/Ring/FreeCommRing.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Making a term in the language of rings from an element of the FreeCommRing

This file defines the function `FirstOrder.Ring.termOfFreeCommRing` which constructs a
`Language.ring.Term α` from an element of `FreeCommRing α`.

The theorem `FirstOrder.Ring.realize_termOfFreeCommRing` shows that the term constructed when
realized in a ring `R` is equal to the lift of the element of `FreeCommRing α` to `R`.
-/

namespace FirstOrder

namespace Ring

open Language

variable {α : Type*}

attribute [local instance] compatibleRingOfRing

set_option backward.privateInPublic true in

private theorem exists_term_realize_eq_freeCommRing (p : FreeCommRing α) :
    ∃ t : Language.ring.Term α,
      (t.realize FreeCommRing.of : FreeCommRing α) = p :=
  FreeCommRing.induction_on p
    ⟨-1, by simp⟩
    (fun a => ⟨Term.var a, by simp [Term.realize]⟩)
    (fun x y ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ =>
      ⟨t₁ + t₂, by simp_all⟩)
    (fun x y ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ =>
      ⟨t₁ * t₂, by simp_all⟩)

end

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

noncomputable def termOfFreeCommRing (p : FreeCommRing α) : Language.ring.Term α :=
  Classical.choose (exists_term_realize_eq_freeCommRing p)

variable {R : Type*} [CommRing R] [CompatibleRing R]
