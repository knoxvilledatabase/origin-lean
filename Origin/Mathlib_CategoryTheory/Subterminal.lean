/-
Extracted from CategoryTheory/Subterminal.lean
Genuine: 9 of 10 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Subterminal objects

Subterminal objects are the objects which can be thought of as subobjects of the terminal object.
In fact, the definition can be constructed to not require a terminal object, by defining `A` to be
subterminal iff for any `Z`, there is at most one morphism `Z ⟶ A`.
An alternate definition is that the diagonal morphism `A ⟶ A ⨯ A` is an isomorphism.
In this file we define subterminal objects and show the equivalence of these three definitions.

We also construct the subcategory of subterminal objects.

## TODO

* Define exponential ideals, and show this subcategory is an exponential ideal.
* Use the above to show that in a locally Cartesian closed category, every subobject lattice
  is Cartesian closed (equivalently, a Heyting algebra).

-/

universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open Limits Category

variable {C : Type u₁} [Category.{v₁} C] {A : C}

def IsSubterminal (A : C) : Prop :=
  ∀ ⦃Z : C⦄ (f g : Z ⟶ A), f = g

theorem IsSubterminal.mono_isTerminal_from (hA : IsSubterminal A) {T : C} (hT : IsTerminal T) :
    Mono (hT.from A) :=
  { right_cancellation := fun _ _ _ => hA _ _ }

theorem IsSubterminal.mono_terminal_from [HasTerminal C] (hA : IsSubterminal A) :
    Mono (terminal.from A) :=
  hA.mono_isTerminal_from terminalIsTerminal

theorem isSubterminal_of_mono_isTerminal_from {T : C} (hT : IsTerminal T) [Mono (hT.from A)] :
    IsSubterminal A := fun Z f g => by
  rw [← cancel_mono (hT.from A)]
  apply hT.hom_ext

theorem isSubterminal_of_mono_terminal_from [HasTerminal C] [Mono (terminal.from A)] :
    IsSubterminal A := fun Z f g => by
  rw [← cancel_mono (terminal.from A)]
  subsingleton

theorem isSubterminal_of_isTerminal {T : C} (hT : IsTerminal T) : IsSubterminal T := fun _ _ _ =>
  hT.hom_ext _ _

theorem isSubterminal_of_terminal [HasTerminal C] : IsSubterminal (⊤_ C) := fun _ _ _ => by
  subsingleton

set_option backward.isDefEq.respectTransparency false in

theorem IsSubterminal.isIso_diag (hA : IsSubterminal A) [HasBinaryProduct A A] : IsIso (diag A) :=
  ⟨⟨Limits.prod.fst,
      ⟨by simp, by
        rw [IsSubterminal.def] at hA
        cat_disch⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in

theorem isSubterminal_of_isIso_diag [HasBinaryProduct A A] [IsIso (diag A)] : IsSubterminal A :=
  fun Z f g => by
  have : (Limits.prod.fst : A ⨯ A ⟶ _) = Limits.prod.snd := by simp [← cancel_epi (diag A)]
  rw [← prod.lift_fst f g, this, prod.lift_snd]
